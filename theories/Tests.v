(** * Tests

    Checks on concrete inputs, by computation.  The first group are
    inputs that must be rejected rather than silently trimmed: a
    template for a function the program does not define, a template
    with more or fewer refinements than parameters, two templates or
    two contracts for one function.  The second group are the measures
    of termination, and malformed measures, rejected in the same way. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Obligation.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Solver Require Import Prove.
From Liquid.Refine Require Import Spec Check Measure.
From Liquid.Liquid Require Import Template Infer.
From Liquid.Examples Require Import Bounded Inc Sum Loop.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition failed {C} (r : ianswer C) : bool := match r with IFailed _ => true | _ => false end.
Definition inferred {C} (r : ianswer C) : bool := match r with Inferred _ _ _ => true | _ => false end.
Definition is_err {A} (r : result string A) : bool := match r with Err _ => true | Ok _ => false end.

(** ** Malformed templates are rejected, not trimmed *)

(** The baseline: the templates of the lecture are inferred. *)
Example infer_sum : inferred (snd (infer prove sum_prog (sum_tspec quals) [])) = true.
Proof. vm_compute. reflexivity. Qed.

(** A template for a function the program does not define. *)
Example infer_unknown_function :
  failed (snd (infer prove sum_prog (sum_tspec quals ++ [("typo", of_contract inc_contract)]) [])) = true.
Proof. vm_compute. reflexivity. Qed.

(** One parameter, two refinements: the second, [false], is not dropped. *)
Definition inc_two_pres : ctemplate :=
  mkCT [fixed ftrue; fixed ffalse] (fixed (c_post inc_contract)).

Example infer_extra_refinement : failed (snd (infer prove inc_prog [("inc", inc_two_pres)] [])) = true.
Proof. vm_compute. reflexivity. Qed.

(** The same contract is rejected by the first algorithm. *)
Example check_extra_refinement :
  accepted (check_prog prove inc_prog [("inc", mkContract [ftrue; ffalse] (c_post inc_contract))]) = false.
Proof. vm_compute. reflexivity. Qed.

(** One parameter short. *)
Example infer_missing_refinement :
  failed (snd (infer prove sum_prog [("go", mkCT [fixed ftrue; fixed len_refinement] (fixed ftrue))] [])) = true.
Proof. vm_compute. reflexivity. Qed.

(** Two templates for [go]: the second, with the bound missing, would
    be ignored. *)
Example infer_duplicate_template :
  failed (snd (infer prove sum_prog (sum_tspec quals ++ [("go", go_template quals_no_lower)]) [])) = true.
Proof. vm_compute. reflexivity. Qed.

(** Two contracts for [f] in the first algorithm: the second, [false]
    on the input, would be ignored. *)
Example check_duplicate_contract :
  accepted (check_prog prove bounded (bounded_spec ++ [("f", mkContract [ffalse] ftrue)])) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Measures of termination *)

(** [n − i] for [go]: non-negative under the invariant, decreasing at
    the recursive call. *)
Example measure_go : accepted (check_measures prove sum_prog sum_spec sum_measures) = true.
Proof. vm_compute. reflexivity. Qed.

Example measure_go_obligations : length (measure_obligations sum_prog sum_spec sum_measures) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(** The invariant [0 ≤ i] alone: the reads are safe, but [n − i] is not
    known to be non-negative. *)
Example lower_contracts : accepted (check_prog prove sum_prog sum_spec_lower) = true.
Proof. vm_compute. reflexivity. Qed.

Example lower_measure : accepted (check_measures prove sum_prog sum_spec_lower sum_measures) = false.
Proof. vm_compute. reflexivity. Qed.

(** [n] does not decrease, [i] increases. *)
Example measure_n : accepted (check_measures prove sum_prog sum_spec [("go", TVar "n")]) = false.
Proof. vm_compute. reflexivity. Qed.

Example measure_i : accepted (check_measures prove sum_prog sum_spec [("go", TVar "i")]) = false.
Proof. vm_compute. reflexivity. Qed.

(** [loop] is accepted by the contracts and has no measure
    ([loop_no_measure] for every measure). *)
Example measure_loop : accepted (check_measures prove loop_prog loop_spec loop_measures) = false.
Proof. vm_compute. reflexivity. Qed.

(** A measure of a function the program does not define: an error, not
    a measure ignored. *)
Example measure_unknown : is_err (check_measures prove sum_prog sum_spec (sum_measures ++ [("typo", TVar "x")])) = true.
Proof. vm_compute. reflexivity. Qed.

(** Two measures for [go]: the second, [n], would be ignored. *)
Example measure_duplicate : is_err (check_measures prove sum_prog sum_spec (sum_measures ++ [("go", TVar "n")])) = true.
Proof. vm_compute. reflexivity. Qed.

(** [j] is a local of the body, not a parameter; [b] is not an array of
    [go]. *)
Example measure_local : is_err (check_measures prove sum_prog sum_spec [("go", TSub (TVar "n") (TVar "j"))]) = true.
Proof. vm_compute. reflexivity. Qed.

Example measure_foreign_array : is_err (check_measures prove sum_prog sum_spec [("go", TSub (TLen "b") (TVar "i"))]) = true.
Proof. vm_compute. reflexivity. Qed.
