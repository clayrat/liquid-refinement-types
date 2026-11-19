(** * Base types

    A checker of base types against the declared signatures: the types
    of the parameters and of the result of every function are given, as
    the plan of the lecture allows (no algorithm W).

    Besides the types, the checker enforces two conventions that the
    generator of obligations relies on:

    - comparisons in a condition are between integers only: [<], [≤]
      and [=] of the logic are defined on integer terms, and an equality
      of booleans would have no image in the hypotheses;
    - every name bound by [let] is fresh: not bound before in its scope,
      not a parameter, and not the reserved name [ν] of the result.
      Then the facts accumulated about a variable stay true after the
      environment is extended, and the generator makes no fresh names.

    Function names are distinct, and so are the parameters of each
    function. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Lang Require Import Syntax Eval.

Local Open Scope string_scope.

Definition tenv : Type := list (string * ty).

(** The name of the result in refinements; programs may not bind it. *)
Definition nu : string := "ν".

Definition reserved (x : string) : bool := String.eqb x nu.

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
