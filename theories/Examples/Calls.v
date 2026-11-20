(** * Two calls with the same argument

      let r₁ = f 0 in let r₂ = f 0 in r₁ − r₂        required: ν = 0

    with the contract of Examples/Bounded.v.  The function is pure and
    deterministic, so the result is [0]; but the names of the results
    are fresh, and the contract only bounds them: the abstract model of
    calls, in which each call returns any result allowed by the
    postcondition, does not give [r₁ = r₂], and the solver refutes the
    obligation with an unreachable counter-model.  The hypothesis
    [d = r₁ − r₂] is outside the difference fragment: the solver
    eliminates [d] first (Solver/Elim.v), the goal becomes
    [r₁ − r₂ = 0], and the counter-model is [r₁ = 1, r₂ = 0, d = 1]
    (Tests.v, [two_calls_refuted]).  No run reaches it: every run that
    ends returns [0] ([client_twice_returns_0]).  This is the
    difference between fresh names of results and the function symbol
    [δ] of the paper. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval EvalFacts.
From Liquid.Refine Require Import Spec Check.

Local Open Scope string_scope.
Local Open Scope Z_scope.
From Liquid.Examples Require Import Bounded.

Definition client_twice : client :=
  mkClient [] [] (lcall "r1" "f" [num 0] (lcall "r2" "f" [num 0] (lsub "d" "r1" "r2" (ERet "d"))))
           (FEq (TVar nu) (TConst 0)).

(** Both calls return [1]; the result is [0] from the fuel [4] on. *)
Lemma client_twice_value : evalFuel 4 bounded [] (cl_expr client_twice) = Value (VInt 0).
Proof. reflexivity. Qed.

(** Whatever fuel ends the run, the result is [0]: the counter-model
    with [d = 1] describes no run. *)
Theorem client_twice_returns_0 : forall k v, evalFuel k bounded [] (cl_expr client_twice) = Value v -> v = VInt 0.
Proof.
  intros k v H. destruct (Nat.le_ge_cases k 4) as [Hk | Hk].
  - pose proof (evalFuel_value_mono k 4 _ _ _ v Hk H) as H4. rewrite client_twice_value in H4. congruence.
  - pose proof (evalFuel_value_mono 4 k _ _ _ _ Hk client_twice_value) as Hk'. congruence.
Qed.
