(** * The bounded increment of the paper, over the integers

      f : {x:Int | 0 ≤ x ∧ x < 2} → {ν:Int | 0 ≤ ν ∧ ν < 4}
      f x = x + 1

      client = let r = f 1 in r + 2        required: ν < 6

    Three obligations: the body against the contract, the input of the
    call, the use of the result.  The body [3] keeps the contract and the
    check of the client; the result of the client changes from 4 to 5.
    [f 2] violates the precondition, and so does [let r = f 2 in 0],
    although the result of the call is not used. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Check.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition f_contract : contract :=
  mkContract [FAnd (FLe (TConst 0) (TVar "x")) (FLt (TVar "x") (TConst 2))]
             (FAnd (FLe (TConst 0) (TVar nu)) (FLt (TVar nu) (TConst 4))).

Definition bounded_spec : spec := [("f", f_contract)].

Definition f_def : fundef := mkFun "f" [("x", TyInt)] TyInt (ladd "y" "x" (num 1) (ERet "y")).
Definition f3_def : fundef := mkFun "f" [("x", TyInt)] TyInt (ERet (num 3)).

Definition bounded : prog := [f_def].
Definition bounded3 : prog := [f3_def].

Definition client_f (n : Z) : client :=
  mkClient [] [] (lcall "r" "f" [num n] (ladd "s" "r" (num 2) (ERet "s"))) (FLt (TVar nu) (TConst 6)).

Definition client_f1 : client := client_f 1.
Definition client_f2 : client := client_f 2.

(** The result of [f 2] is not used. *)
Definition client_f2_dropped : client := mkClient [] [] (lcall "r" "f" [num 2] (ERet (num 0))) ftrue.
