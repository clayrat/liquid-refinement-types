(** * Templates of contracts

    A refinement of a template is a fixed part and, possibly, a hole: an
    unknown [κ] with its finite list of qualifiers.  [instantiate]
    replaces every hole by an application of [κ] to the parameters
    visible at that place, of the integer and boolean sorts:

    - for the refinement of a parameter [x], [x] itself (if it is of
      these sorts) and then the parameters before it, in order;
    - for the refinement of the result, [ν] (if the result is of these
      sorts) and then all the parameters.

    The sorts are written in the signature of [κ], and the formal
    parameters of [κ] have the names of these variables, so the
    qualifiers are written over the variables of the program: the hole
    of [i] in [go a n i] is [κ(i, n)], with qualifiers such as [0 ≤ i]
    or [i < n].  The arrays and lists are not arguments of [κ] in this
    version.

    [instantiate] rejects, rather than drops, a template it cannot
    turn into a contract.  [kdecls_ok] checks the qualifiers:
    well-sorted formulas whose free names are formal parameters,
    without unknowns ([kdecls_ok_quals]), and distinct names of
    unknowns.  Patterns of qualifiers instantiated by the variables in
    scope are the next step. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing.
From Liquid.Refine Require Import Spec.
From Liquid.Liquid Require Import Horn Weaken.

Local Open Scope string_scope.
Local Open Scope list_scope.

Record hole : Type := mkHole {
  hl_name : string;
  hl_quals : list formula
}.

Record rtemplate : Type := mkRT {
  rt_fixed : formula;
  rt_hole : option hole
}.

Record ctemplate : Type := mkCT {
  ct_pre : list rtemplate;
  ct_post : rtemplate
}.

Definition tspec : Type := list (string * ctemplate).

Definition fixed (p : formula) : rtemplate := mkRT p None.
Definition holed (p : formula) (h : hole) : rtemplate := mkRT p (Some h).

(** A contract without holes as a template. *)
Definition of_contract (c : contract) : ctemplate := mkCT (map fixed (c_pre c)) (fixed (c_post c)).

Definition sort_of (T : ty) : option sort :=
  match T with TyInt => Some SInt | TyBool => Some SBool | _ => None end.

Definition sorted (Γ : tenv) : list (string * sort) :=
  flat_map (fun p => match sort_of (snd p) with Some s => [(fst p, s)] | None => [] end) Γ.

Definition formal_arg (f : string * sort) : arg :=
  match snd f with SInt => UInt (TVar (fst f)) | SBool => UBool (BVar (fst f)) end.

(** The refinement of a template at a place with the visible variables
    [vis], the refined one first; the declaration of its [κ]. *)
Definition inst_rt (vis : tenv) (rt : rtemplate) : formula * list kdecl :=
  match rt_hole rt with
  | None => (rt_fixed rt, [])
  | Some h =>
      let fs := sorted vis in
      (fand (rt_fixed rt) (FKappa (hl_name h) (map formal_arg fs)), [mkKDecl (hl_name h) fs (hl_quals h)])
  end.

(** The refinements of the parameters: exactly one template per
    parameter, otherwise an error; nothing is dropped. *)
Fixpoint inst_pres (seen : tenv) (ps : tenv) (rts : list rtemplate) : result string (list formula * list kdecl) :=
  match ps, rts with
  | [], [] => Ok ([], [])
  | p :: ps', rt :: rts' =>
      let (q, ds) := inst_rt (p :: seen) rt in
      let* r := inst_pres (seen ++ [p]) ps' rts' in
      Ok (q :: fst r, ds ++ snd r)
  | _, _ => Err "the number of refinements differs from the number of parameters"
  end.

Definition inst_ct (fd : fundef) (ct : ctemplate) : result string (contract * list kdecl) :=
  let* r := map_err (fun why => (why ++ " in the template of " ++ fd_name fd)%string) (inst_pres [] (fd_params fd) (ct_pre ct)) in
  let (post, ds2) := inst_rt ((nu, fd_ret fd) :: fd_params fd) (ct_post ct) in
  Ok (mkContract (fst r) post, snd r ++ ds2).

Definition inst_entry (P : prog) (e : string * ctemplate) : result string ((string * contract) * list kdecl) :=
  match find_fun (fst e) P with
  | Some fd =>
      let* r := inst_ct fd (snd e) in
      Ok ((fst e, fst r), snd r)
  | None => Err ("a template for an unknown function: " ++ fst e)%string
  end.

(** The contracts with unknowns of a program, and the declarations of
    the unknowns.  Every template becomes a contract: a template for a
    function the program does not define, a second template for the
    same function, or a number of refinements of the parameters other
    than the arity is an error ([instantiate_complete]). *)
Definition instantiate (P : prog) (T : tspec) : result string (spec * list kdecl) :=
  let* _ := require (distinct (map fst T)) "two templates for one function" in
  let* es := mapM (inst_entry P) T in
  Ok (map fst es, flat_map snd es).

Lemma inst_pres_length : forall seen ps rts r, inst_pres seen ps rts = Ok r ->
  length (fst r) = length ps /\ length rts = length ps.
Proof.
  intros seen ps. revert seen. induction ps as [|p ps IH]; intros seen [|rt rts] r H; cbn in H; try discriminate H.
  - injection H as <-. split; reflexivity.
  - destruct (inst_rt (p :: seen) rt) as [q ds]. bind_in H r' Hr'. injection H as <-. cbn.
    destruct (IH _ _ _ Hr') as [H1 H2]. split; f_equal; assumption.
Qed.

Theorem instantiate_complete : forall P T S D, instantiate P T = Ok (S, D) ->
  distinct (map fst T) = true /\
  Forall2 (fun e se => fst se = fst e /\
             exists fd, find_fun (fst e) P = Some fd /\
                        length (ct_pre (snd e)) = length (fd_params fd) /\
                        length (c_pre (snd se)) = length (fd_params fd)) T S.
Proof.
  intros P T S D H. unfold instantiate in H.
  bind_in H u Hd. bind_in H es Hes. injection H as <- _.
  split; [exact (require_ok _ _ _ Hd) | ].
  apply mapM_ok in Hes. clear Hd. induction Hes as [|e x T' es' Hx _ IH]; cbn;
    [apply Forall2_nil | apply Forall2_cons; [ | exact IH]].
  unfold inst_entry in Hx. destruct (find_fun (fst e) P) as [fd | ] eqn:Ef; [ | discriminate Hx].
  bind_in Hx r Hr. injection Hx as <-. cbn. split; [reflexivity | ].
  exists fd. split; [reflexivity | ].
  unfold inst_ct in Hr. bind_in Hr r' Hr'. apply map_err_ok in Hr'.
  destruct (inst_rt _ (ct_post (snd e))) as [post ds2]. injection Hr as <-. cbn.
  destruct (inst_pres_length _ _ _ _ Hr') as [H1 H2]. split; assumption.
Qed.

Definition ksig_of (D : list kdecl) : ksig := map (fun d => (kd_name d, map snd (kd_formals d))) D.

Definition scope_of_formals (fs : list (string * sort)) : scope :=
  mkScope (map fst (filter (fun f => if sort_eq_dec (snd f) SInt then true else false) fs))
          (map fst (filter (fun f => if sort_eq_dec (snd f) SBool then true else false) fs))
          [].

Definition kdecls_ok (D : list kdecl) : bool :=
  distinct (map kd_name D)
  && forallb (fun d => forallb (formula_ok [] (scope_of_formals (kd_formals d))) (kd_quals d)) D.

(** Checked declarations have qualifiers without unknowns, as
    [weaken_kfree_queries] requires. *)
Lemma kdecls_ok_quals : forall D, kdecls_ok D = true -> quals_kfree D.
Proof.
  intros D H. unfold kdecls_ok in H. apply andb_prop in H as [_ H]. rewrite forallb_forall in H.
  apply Forall_forall. intros d Hd. specialize (H d Hd). rewrite forallb_forall in H.
  apply Forall_forall. intros q Hq. exact (formula_ok_kfree _ q (H q Hq)).
Qed.

(** The contracts with a solution substituted for the unknowns. *)
Definition apply_spec (D : list kdecl) (sol : solution) (S : spec) : spec :=
  map (fun e => (fst e, mkContract (map (apply_sol D sol) (c_pre (snd e))) (apply_sol D sol (c_post (snd e))))) S.
