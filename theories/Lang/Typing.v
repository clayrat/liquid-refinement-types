(** * Base types

    A checker of base types against the declared signatures: the types
    of the parameters and of the result of every function are given, as
    the plan of the lecture allows (no algorithm W).

    Besides the types, the checker enforces two conventions that the
    generator of obligations relies on:

    - comparisons in a condition are between integers only: [<], [≤]
      and [=] of the logic are defined on integer terms, and an equality
      of booleans would have no image in the hypotheses;
    - every name bound by [let] or [match] is fresh: not bound before in
      its scope, not a parameter, and not reserved ([reserved]): neither
      the name [ν] of the result nor a name with a dot.  Then the facts
      accumulated about a variable stay true after the environment is
      extended, and the generator needs no fresh names of its own: the
      copies [r.x] of the parameters of a call under the rule [RuleRoot]
      (Refine/Wp.v) are reserved ([reserved_copy]), so no program or
      client binds them, and the copies of two calls on one path differ
      ([copy_inj]).  Parameters and the variables of a client are
      checked against [reserved] too.

    Function names are distinct, and so are the parameters of each
    function. *)

From Stdlib Require Import String Ascii List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Lang Require Import Syntax Eval.

Local Open Scope string_scope.

Definition tenv : Type := list (string * ty).

(** The name of the result in refinements; programs may not bind it. *)
Definition nu : string := "ν".

Fixpoint has_dot (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => Ascii.eqb c "."%char || has_dot s'
  end.

(** The names a program or a client may not bind: [ν], and the names
    with a dot, which belong to the generator. *)
Definition reserved (x : string) : bool := String.eqb x nu || has_dot x.

Lemma reserved_nu : reserved nu = true.
Proof. reflexivity. Qed.

(** The copy [r.x] of a parameter [x] at the call [let r = f(ā)] is
    reserved. *)
Lemma reserved_copy : forall r x, reserved (r ++ "." ++ x) = true.
Proof.
  intros r x. unfold reserved. apply orb_true_iff. right.
  induction r as [|c r IH]; cbn in *; [reflexivity | rewrite IH, orb_true_r; reflexivity].
Qed.

(** Names without a dot give distinct copies. *)
Lemma copy_inj : forall r1 r2 x1 x2, has_dot r1 = false -> has_dot r2 = false ->
  (r1 ++ "." ++ x1 = r2 ++ "." ++ x2)%string -> r1 = r2 /\ x1 = x2.
Proof.
  induction r1 as [|c1 r1 IH]; intros [|c2 r2] x1 x2 H1 H2 E; cbn in H1, H2, E.
  - injection E as ->. split; reflexivity.
  - injection E as <- _. discriminate H2.
  - injection E as -> _. discriminate H1.
  - injection E as <- E. apply orb_false_iff in H1 as [_ H1]. apply orb_false_iff in H2 as [_ H2].
    destruct (IH r2 x1 x2 H1 H2 E) as [-> ->]. split; reflexivity.
Qed.

Definition atom_ty (Γ : tenv) (a : atom) : option ty :=
  match a with
  | AVar x => lookup x Γ
  | ANum _ => Some TyInt
  | ABool _ => Some TyBool
  | AUnit => Some TyUnit
  end.

Fixpoint atoms_ty (Γ : tenv) (args : list atom) : option (list ty) :=
  match args with
  | [] => Some []
  | a :: args' =>
      match atom_ty Γ a, atoms_ty Γ args' with
      | Some T, Some Ts => Some (T :: Ts)
      | _, _ => None
      end
  end.

Definition tys_eqb (Ts Us : list ty) : bool :=
  if list_eq_dec ty_eq_dec Ts Us then true else false.

Definition args_ok (Γ : tenv) (args : list atom) (Ts : list ty) : bool :=
  match atoms_ty Γ args with Some Us => tys_eqb Us Ts | None => false end.

Definition prim_sig (p : prim) : list ty * ty :=
  match p with
  | PAdd | PSub => ([TyInt; TyInt], TyInt)
  | PLength => ([TyArr], TyInt)
  | PGet => ([TyArr; TyInt], TyInt)
  | PNil => ([], TyList)
  | PCons => ([TyInt; TyList], TyList)
  end.

Definition cond_ok (Γ : tenv) (c : cond) : bool :=
  match c with
  | CAtom a => args_ok Γ [a] [TyBool]
  | CCmp _ a1 a2 => args_ok Γ [a1; a2] [TyInt; TyInt]
  end.

Definition fresh_ok (Γ : tenv) (x : string) : bool :=
  negb (reserved x) && match lookup x Γ with Some _ => false | None => true end.

Fixpoint ty_expr (P : prog) (Γ : tenv) (e : expr) : result string ty :=
  match e with
  | ERet a =>
      match atom_ty Γ a with
      | Some T => Ok T
      | None => Err "unbound variable"
      end
  | EPrim x p args e' =>
      let* _ := require (args_ok Γ args (fst (prim_sig p))) ("arguments of " ++ prim_name p) in
      let* _ := require (fresh_ok Γ x) ("name not fresh: " ++ x) in
      ty_expr P ((x, snd (prim_sig p)) :: Γ) e'
  | ECall x f args e' =>
      match find_fun f P with
      | None => Err ("unknown function " ++ f)
      | Some fd =>
          let* _ := require (args_ok Γ args (map snd (fd_params fd))) ("arguments of " ++ f) in
          let* _ := require (fresh_ok Γ x) ("name not fresh: " ++ x) in
          ty_expr P ((x, fd_ret fd) :: Γ) e'
      end
  | EIf c e1 e2 =>
      let* _ := require (cond_ok Γ c) "condition" in
      let* T1 := ty_expr P Γ e1 in
      let* T2 := ty_expr P Γ e2 in
      let* _ := require (ty_eqb T1 T2) "branches of different types" in
      Ok T1
  | EMatch x e1 h t e2 =>
      let* _ := require (match lookup x Γ with Some TyList => true | _ => false end) ("match on " ++ x) in
      let* _ := require (fresh_ok Γ h) ("name not fresh: " ++ h) in
      let* _ := require (fresh_ok ((h, TyInt) :: Γ) t) ("name not fresh: " ++ t) in
      let* T1 := ty_expr P Γ e1 in
      let* T2 := ty_expr P ((t, TyList) :: (h, TyInt) :: Γ) e2 in
      let* _ := require (ty_eqb T1 T2) "branches of different types" in
      Ok T1
  end.

Fixpoint distinct (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (existsb (String.eqb x) xs') && distinct xs'
  end.

Definition ty_fun (P : prog) (fd : fundef) : result string unit :=
  let* _ := require (distinct (map fst (fd_params fd))) ("parameters of " ++ fd_name fd) in
  let* _ := require (forallb (fun x => negb (reserved x)) (map fst (fd_params fd)))
                    ("reserved parameter in " ++ fd_name fd) in
  let* T := ty_expr P (fd_params fd) (fd_body fd) in
  require (ty_eqb T (fd_ret fd)) ("result of " ++ fd_name fd).

Definition ty_prog (P : prog) : result string unit :=
  let* _ := require (distinct (map fd_name P)) "function names" in
  let* _ := mapM (ty_fun P) P in
  Ok tt.

(** ** Inversion *)

Lemma ty_eqb_eq : forall T U, ty_eqb T U = true -> T = U.
Proof. intros T U H. unfold ty_eqb in H. now destruct (ty_eq_dec T U). Qed.

Lemma ty_eqb_refl : forall T, ty_eqb T T = true.
Proof. intros T. unfold ty_eqb. now destruct (ty_eq_dec T T). Qed.

Lemma tys_eqb_eq : forall Ts Us, tys_eqb Ts Us = true -> Ts = Us.
Proof. intros Ts Us H. unfold tys_eqb in H. now destruct (list_eq_dec ty_eq_dec Ts Us). Qed.

Lemma args_ok_atoms_ty : forall Γ args Ts, args_ok Γ args Ts = true -> atoms_ty Γ args = Some Ts.
Proof.
  intros Γ args Ts H. unfold args_ok in H.
  destruct (atoms_ty Γ args) as [Us | ]; [ | discriminate H]. now rewrite (tys_eqb_eq _ _ H).
Qed.

Lemma find_fun_in : forall f P fd, find_fun f P = Some fd -> In fd P.
Proof.
  intros f P. induction P as [|d P IH]; cbn; intros fd H; [discriminate H | ].
  destruct (String.eqb f (fd_name d)); [injection H as <-; now left | right; auto].
Qed.

Lemma ty_prog_fun : forall P fd, ty_prog P = Ok tt -> In fd P -> ty_fun P fd = Ok tt.
Proof.
  intros P fd H Hin. unfold ty_prog in H.
  bind_in H u1 H1. bind_in H us Hus.
  apply mapM_ok in Hus.
  assert (Hgen : forall l us', Forall2 (fun a b => ty_fun P a = Ok b) l us' -> In fd l -> ty_fun P fd = Ok tt).
  { intros l us' Hl. induction Hl as [|d u l' us'' Hd _ IH]; intros Hi; [destruct Hi | ].
    destruct Hi as [<- | Hi]; [destruct u; exact Hd | auto]. }
  exact (Hgen P us Hus Hin).
Qed.

(** ** Distinct and fresh names *)

Lemma distinct_NoDup : forall xs, distinct xs = true -> NoDup xs.
Proof.
  intros xs. induction xs as [|x xs IH]; cbn; intros H; [constructor | ].
  apply andb_prop in H as [H1 H2]. constructor; [ | exact (IH H2)].
  intros Hin. rewrite negb_true_iff in H1. assert (existsb (String.eqb x) xs = true); [ | congruence].
  apply existsb_exists. exists x. split; [exact Hin | apply String.eqb_refl].
Qed.

Lemma not_reserved_nu : forall xs, forallb (fun x => negb (reserved x)) xs = true -> ~ In nu xs.
Proof.
  intros xs H Hin. rewrite forallb_forall in H. specialize (H nu Hin). rewrite reserved_nu in H.
  discriminate H.
Qed.

Lemma fresh_ok_inv : forall Γ x, fresh_ok Γ x = true -> lookup x Γ = None /\ x <> nu.
Proof.
  intros Γ x H. unfold fresh_ok in H. apply andb_prop in H as [H1 H2].
  split; [destruct (lookup x Γ); [discriminate H2 | reflexivity] | ].
  intros ->. rewrite reserved_nu in H1. discriminate H1.
Qed.
