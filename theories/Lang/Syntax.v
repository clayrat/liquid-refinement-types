(** * The language: first order, by value, in ANF

      a ::= x | n | true | false | ()
      c ::= a | a₁ < a₂ | a₁ ≤ a₂ | a₁ = a₂
      e ::= ret a
          | let x = op(a₁, …, aₖ) in e      op ∈ {+, −, length, get}
          | let x = f(a₁, …, aₖ) in e
          | if c then e₁ else e₂

    The condition of a branch is an atom or a comparison of atoms, so
    that it enters the hypotheses as a ready atom of the logic: writing
    [let b = i < n in if b …] would give the hypothesis [b ⇔ i < n],
    a disjunction outside the difference fragment.

    A program is a list of top-level definitions: a name, parameters with
    their base types, the type of the result and the body.  A function
    may call any function of the list, itself included; there are no
    local functions.  Arrays are immutable arrays of integers.

    The contracts are not here: [prog] has no refinements, and the
    evaluator of Lang/Eval.v takes a [prog] only.  Independence of the
    annotations holds by the type of the evaluator.

    Programs are built with the constructors and the helpers at the end
    of the file; names are strings. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.

Inductive ty : Type := TyInt | TyBool | TyUnit | TyArr.

Definition ty_eq_dec (t1 t2 : ty) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Definition ty_eqb (t1 t2 : ty) : bool := if ty_eq_dec t1 t2 then true else false.

Inductive atom : Type :=
| AVar (x : string)
| ANum (z : Z)
| ABool (b : bool)
| AUnit.

Inductive cmp : Type := CLt | CLe | CEq.

Inductive cond : Type :=
| CAtom (a : atom)
| CCmp (c : cmp) (a1 a2 : atom).

Inductive prim : Type := PAdd | PSub | PLength | PGet.

Inductive expr : Type :=
| ERet (a : atom)
| EPrim (x : string) (p : prim) (args : list atom) (e : expr)
| ECall (x : string) (f : string) (args : list atom) (e : expr)
| EIf (c : cond) (e1 e2 : expr).

Record fundef : Type := mkFun {
  fd_name : string;
  fd_params : list (string * ty);
  fd_ret : ty;
  fd_body : expr
}.

Definition prog : Type := list fundef.

Fixpoint find_fun (f : string) (P : prog) : option fundef :=
  match P with
  | [] => None
  | d :: P' => if String.eqb f (fd_name d) then Some d else find_fun f P'
  end.

Definition prim_name (p : prim) : string :=
  match p with PAdd => "+" | PSub => "-" | PLength => "length" | PGet => "get" end.

(** ** Helpers for writing programs *)

Coercion AVar : string >-> atom.

Definition num (z : Z) : atom := ANum z.
Definition ladd (x : string) (a b : atom) (e : expr) : expr := EPrim x PAdd [a; b] e.
Definition lsub (x : string) (a b : atom) (e : expr) : expr := EPrim x PSub [a; b] e.
Definition llength (x : string) (a : atom) (e : expr) : expr := EPrim x PLength [a] e.
Definition lget (x : string) (a i : atom) (e : expr) : expr := EPrim x PGet [a; i] e.
Definition lcall (x : string) (f : string) (args : list atom) (e : expr) : expr := ECall x f args e.
Definition ifc (c : cmp) (a1 a2 : atom) (e1 e2 : expr) : expr := EIf (CCmp c a1 a2) e1 e2.
