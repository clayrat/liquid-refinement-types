(** * Contracts

    A contract of a function is a refinement of every parameter, which
    may mention the parameters before it and itself, and a refinement of
    the result over the parameters and [ν]:

      x₁:{x₁:B₁ | P₁(x₁)} → … → xₙ:{xₙ:Bₙ | Pₙ(x₁, …, xₙ)} → {ν:C | R(x₁, …, xₙ, ν)}

    The refinements mention the parameters by name: an integer parameter
    is an integer variable of the logic, a boolean parameter a boolean
    variable, an array parameter the name of an array under [len]; a
    parameter of type Unit has no logical occurrences.  A function with
    no entry in the table has the contract [true] everywhere.

    The primitives have contracts of the same form in their own table
    ([prim_contract]): addition and subtraction have the precondition
    [true] and the exact result; [length] the precondition [true] and
    [ν = len a ∧ 0 ≤ ν]; [get] the precondition [0 ≤ i ∧ i < len a]
    and the postcondition [true]: the logic of this version says nothing
    about the contents of arrays.

    A call instantiates a contract by a sorted substitution of the
    formal parameters by the actual atoms ([inst_subst]), and of [ν] by
    the name of the result ([res_subst]): [Pre_f(ā)] and [Post_f(ā, r)].

    [contract_ok] checks the scopes and sorts of a contract against the
    signature of its function; the unknowns [κ] a contract may contain
    (Liquid/Template.v) are checked against their signature [K]. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing.

Local Open Scope string_scope.
Local Open Scope list_scope.

Record contract : Type := mkContract {
  c_pre : list formula;
  c_post : formula
}.

Definition spec : Type := list (string * contract).

Definition default_contract (ps : list (string * ty)) : contract :=
  mkContract (map (fun _ => ftrue) ps) ftrue.

Definition contract_of (S : spec) (fd : fundef) : contract :=
  match assoc (fd_name fd) S with
  | Some c => c
  | None => default_contract (fd_params fd)
  end.

(** ** Contracts of the primitives *)

Definition prim_params (p : prim) : list (string * ty) :=
  match p with
  | PAdd | PSub => [("x", TyInt); ("y", TyInt)]
  | PLength => [("a", TyArr)]
  | PGet => [("a", TyArr); ("i", TyInt)]
  end.

Definition prim_contract (p : prim) : contract :=
  match p with
  | PAdd => mkContract [ftrue; ftrue] (FEq (TVar nu) (TAdd (TVar "x") (TVar "y")))
  | PSub => mkContract [ftrue; ftrue] (FEq (TVar nu) (TSub (TVar "x") (TVar "y")))
  | PLength => mkContract [ftrue] (FAnd (FEq (TVar nu) (TLen "a")) (FLe (TConst 0) (TVar nu)))
  | PGet => mkContract [ftrue; FAnd (FLe (TConst 0) (TVar "i")) (FLt (TVar "i") (TLen "a"))] ftrue
  end.

(** ** From program atoms to the logic *)

Definition aterm (a : atom) : term :=
  match a with
  | AVar x => TVar x
  | ANum z => TConst z
  | _ => TConst 0
  end.

Definition abatom (a : atom) : batom :=
  match a with
  | AVar x => BVar x
  | ABool b => BConst b
  | _ => BConst false
  end.

(** The substitution of a name of type [T] by an atom. *)
Definition bind_atom (x : string) (T : ty) (a : atom) (σ : subst) : subst :=
  match T, a with
  | TyInt, _ => add_int x (aterm a) σ
  | TyBool, _ => add_bool x (abatom a) σ
  | TyArr, AVar y => add_arr x y σ
  | _, _ => σ
  end.

Fixpoint inst_subst (ps : list (string * ty)) (args : list atom) : subst :=
  match ps, args with
  | (x, T) :: ps', a :: args' => bind_atom x T a (inst_subst ps' args')
  | _, _ => subst_empty
  end.

Definition res_subst (T : ty) (r : string) (σ : subst) : subst := bind_atom nu T (AVar r) σ.

Definition pre_inst (c : contract) (ps : list (string * ty)) (args : list atom) : formula :=
  fconj (map (fsubst (inst_subst ps args)) (c_pre c)).

Definition post_inst (c : contract) (ps : list (string * ty)) (ret : ty) (args : list atom) (r : string)
  : formula :=
  fsubst (res_subst ret r (inst_subst ps args)) (c_post c).

(** The refinement [ψ] of a result, at [return a]: [ψ[a/ν]]. *)
Definition ret_inst (T : ty) (a : atom) (ψ : formula) : formula := fsubst (bind_atom nu T a subst_empty) ψ.

Definition atom_type (Γ : tenv) (a : atom) : ty :=
  match atom_ty Γ a with Some T => T | None => TyUnit end.

(** The condition of a branch as a formula. *)
Definition cond_formula (c : cond) : formula :=
  match c with
  | CAtom a => FAtom (abatom a)
  | CCmp CLt a1 a2 => FLt (aterm a1) (aterm a2)
  | CCmp CLe a1 a2 => FLe (aterm a1) (aterm a2)
  | CCmp CEq a1 a2 => FEq (aterm a1) (aterm a2)
  end.

(** ** Scopes and sorts *)

Definition names_of (T : ty) (Γ : tenv) : list string := map fst (filter (fun p => ty_eqb (snd p) T) Γ).

Definition scope_of (Γ : tenv) : scope := mkScope (names_of TyInt Γ) (names_of TyBool Γ) (names_of TyArr Γ).

Fixpoint pres_ok (K : ksig) (seen : tenv) (ps : tenv) (pres : list formula) : bool :=
  match ps, pres with
  | [], [] => true
  | p :: ps', q :: pres' => formula_ok K (scope_of (seen ++ [p])) q && pres_ok K (seen ++ [p]) ps' pres'
  | _, _ => false
  end.

Definition contract_ok (K : ksig) (ps : tenv) (ret : ty) (c : contract) : bool :=
  pres_ok K [] ps (c_pre c) && formula_ok K (scope_of (ps ++ [(nu, ret)])) (c_post c).

(** Every entry of the table names a function of the program, once:
    a second entry for the same function would be ignored by
    [contract_of], so it is an error. *)
Definition spec_ok (K : ksig) (P : prog) (S : spec) : bool :=
  distinct (map fst S)
  && forallb (fun e => match find_fun (fst e) P with Some _ => true | None => false end) S
  && forallb (fun fd => contract_ok K (fd_params fd) (fd_ret fd) (contract_of S fd)) P.

(** The hypotheses of a body: the refinements of the parameters. *)
Definition extend (φ : list formula) (h : formula) : list formula :=
  if is_ftrue h then φ else φ ++ [h].

Definition pre_hyps (c : contract) : list formula := fold_left extend (c_pre c) [].
