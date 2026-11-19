(** * Two calls with the same argument

      let r₁ = f 0 in let r₂ = f 0 in r₁ − r₂        required: ν = 0

    with the contract of Examples/Bounded.v.  The function is pure and
    deterministic, so the result is [0]; but the names of the results
    are fresh, and the contract only bounds them: the abstract model of
    calls, in which each call returns any result allowed by the
    postcondition, does not give [r₁ = r₂], and the solver refutes the
    obligation with an unreachable counter-model.  This is the
    difference between fresh names of results and the function symbol
    [δ] of the paper. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Check.

Local Open Scope string_scope.
Local Open Scope Z_scope.
From Liquid.Examples Require Import Bounded.

Definition client_twice : client :=
  mkClient [] [] (lcall "r1" "f" [num 0] (lcall "r2" "f" [num 0] (lsub "d" "r1" "r2" (ERet "d"))))
           (FEq (TVar nu) (TConst 0)).
