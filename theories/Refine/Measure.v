(** * Measures of termination

    An optional annotation of a recursive function is an integer term
    over its parameters.  [measure_obligations] adds two kinds of
    obligations for every annotated function [f] with measure [μ]:

    - [μ] is non-negative under the refinements of the parameters;
    - at every recursive call [let x = f(ā)], under the hypotheses
      accumulated by the walk of the generator, [μ[ā/x̄] < μ].

    The walk is the one of [gen] (Refine/Gen.v): the same hypotheses are
    added at the same places, so the decrease may use the conditions of
    the branches and the postconditions of the calls before.  For [go]
    with the measure [n − i] both obligations are in the difference
    fragment.

    [check_measures] rejects, rather than ignores, a measure of a
    function the program does not define, a second measure of the same
    function, and a measure whose names are not the integer parameters
    and the arrays of the function.

    The obligations of measure are a check of their own: the acceptance
    of the contracts does not imply termination.  [loop] is accepted
    with the postcondition [false] and has no measure: at its call the
    argument is the parameter itself, and [μ < μ] is refuted whatever
    [μ] is ([loop_no_measure] in Examples/Loop.v).

    That valid obligations of measure imply termination is stated as
    [measures_terminate] and left open (Contracts.v lists it as
    [measures_imply_termination]): besides the measures of the
    recursive functions it needs an order of the dependencies between
    functions, here a rank that every call other than a recursive one
    decreases.  Examples/Sum.v proves the termination of [sum] directly,
    with the fuel it needs; Examples/Loop.v proves that [loop] times out
    for every fuel. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing EvalFacts.
From Liquid.Refine Require Import Spec Wp Gen Check Sound.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition measures : Type := list (string * term).

Section Measure.
  Variable P : prog.
  Variable S : spec.

  (** The decrease at the recursive calls of [f], whose parameters are
      [ps] and measure [μ]. *)
  Fixpoint decreases (f : string) (ps : tenv) (μ : term) (Γ : tenv) (φ : list formula) (e : expr)
    : list obligation :=
    match e with
    | ERet _ => []
    | EPrim x p args e' =>
        let c := prim_contract p in
        let T := snd (prim_sig p) in
        decreases f ps μ ((x, T) :: Γ) (extend φ (post_inst c (prim_params p) T args x)) e'
    | ECall x g args e' =>
        match find_fun g P with
        | Some fd =>
            let c := contract_of S fd in
            let here := if String.eqb g f
                        then emit (LMeasureDecr f x) φ (FLt (tsubst (inst_subst ps args) μ) μ)
                        else [] in
            here ++ decreases f ps μ ((x, fd_ret fd) :: Γ)
                                (extend φ (post_inst c (fd_params fd) (fd_ret fd) args x)) e'
        | None => []
        end
    | EIf c e1 e2 =>
        decreases f ps μ Γ (extend φ (cond_formula c)) e1 ++ decreases f ps μ Γ (extend φ (FNot (cond_formula c))) e2
    end.

  Definition fun_measure_obligations (fd : fundef) (μ : term) : list obligation :=
    let c := contract_of S fd in
    emit (LMeasureNonneg (fd_name fd)) (pre_hyps c) (FLe (TConst 0) μ)
      ++ decreases (fd_name fd) (fd_params fd) μ (fd_params fd) (pre_hyps c) (fd_body fd).

  Definition measure_obligations (M : measures) : list obligation :=
    flat_map (fun fd => match assoc (fd_name fd) M with
                        | Some μ => fun_measure_obligations fd μ
                        | None => []
                        end) P.
End Measure.

(** A measure names a function of the program, and its names are the
    integer parameters and, under [len], the arrays of that function. *)
Definition measure_ok (P : prog) (m : string * term) : result string unit :=
  match find_fun (fst m) P with
  | Some fd => require (formula_ok [] (scope_of (fd_params fd)) (FLe (TConst 0) (snd m)))
                       ("the measure of " ++ fst m ++ ": scope or sorts")%string
  | None => Err ("a measure of an unknown function: " ++ fst m)%string
  end.

Section Check.
  Context {C : Type} (oracle : obligation -> verdict C).

  (** The checks of [check_prog], then those of the measures; every
      measure is checked, none is dropped. *)
  Definition check_measures (P : prog) (S : spec) (M : measures) : result string (list (obligation * verdict C)) :=
    let* _ := ty_prog P in
    let* _ := require (spec_ok [] P S) "the contracts: scope or sorts" in
    let* _ := require (distinct (map fst M)) "two measures for one function" in
    let* _ := mapM (measure_ok P) M in
    Ok (judge oracle (measure_obligations P S M)).
End Check.

(** Every measure of an accepted table is turned into obligations, and
    all of them are proved. *)
Lemma check_measures_complete : forall {C} (oracle : obligation -> verdict C) P S M,
  accepted (check_measures oracle P S M) = true ->
  distinct (map fst M) = true /\
  Forall (fun m => exists fd, find_fun (fst m) P = Some fd) M /\
  forall ob, In ob (measure_obligations P S M) -> is_proved (oracle ob) = true.
Proof.
  intros C oracle P S M H. unfold accepted, check_measures in H.
  destruct (ty_prog P) as [[] | e]; [ | discriminate H]. cbn in H.
  destruct (spec_ok [] P S); [ | discriminate H]. cbn in H.
  destruct (distinct (map fst M)) eqn:Ed; [ | discriminate H]. cbn in H.
  destruct (mapM (measure_ok P) M) as [us | e] eqn:Em; [ | discriminate H]. cbn in H.
  split; [reflexivity | split].
  - apply mapM_ok in Em. clear Ed H. induction Em as [|m u M' us' Hm _ IH]; constructor; [ | exact IH].
    unfold measure_ok in Hm. destruct (find_fun (fst m) P) as [fd | ]; [exists fd; reflexivity | discriminate Hm].
  - intros ob Hin. unfold all_proved, judge in H. rewrite forallb_forall in H.
    exact (H (ob, oracle ob) (in_map (fun ob => (ob, oracle ob)) _ _ Hin)).
Qed.

(** ** The open contract *)

(** The functions called by a body. *)
Fixpoint callees (e : expr) : list string :=
  match e with
  | ERet _ => []
  | EPrim _ _ _ e' => callees e'
  | ECall _ g _ e' => g :: callees e'
  | EIf _ e1 e2 => callees e1 ++ callees e2
  end.

(** An order of the dependencies: a body calls its own function or
    functions of a lower rank. *)
Definition ranked (P : prog) (rank : string -> nat) : Prop :=
  forall fd g, In fd P -> In g (callees (fd_body fd)) -> g = fd_name fd \/ (rank g < rank (fd_name fd))%nat.

(** A typed program accepted with its contracts, whose recursive
    functions have measures with proved obligations and whose other
    calls follow an order, terminates on every input of the types of the
    parameters that satisfies the preconditions.  Open. *)
Definition measures_terminate : Prop :=
  forall C (oracle : obligation -> verdict C) P S M rank,
    oracle_sound oracle ->
    accepted (check_prog oracle P S) = true ->
    accepted (check_measures oracle P S M) = true ->
    ranked P rank ->
    (forall fd, In fd P -> In (fd_name fd) (callees (fd_body fd)) -> In (fd_name fd) (map fst M)) ->
    forall fd vs ρf, In fd P -> bind_params (fd_params fd) vs = Some ρf ->
      Forall2 has_ty vs (map snd (fd_params fd)) ->
      Forall (hold ρf) (c_pre (contract_of S fd)) ->
      exists k v, evalFuel k P ρf (fd_body fd) = Value v.
