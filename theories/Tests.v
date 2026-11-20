(** * Tests

    Checks on concrete inputs, by computation.  The first group are
    inputs that must be rejected rather than silently trimmed: a
    template for a function the program does not define, a template
    with more or fewer refinements than parameters, two templates or
    two contracts for one function.  The second group are the measures
    of termination, and malformed measures, rejected in the same way.
    The third group is stage 8: the elimination of equalities in the
    solver, its certificates checked, and the typing of lists.  The
    fourth group refuses to bind the names reserved for the generator,
    the copies [r.x] of the rule [RuleRoot].  Then clients checked
    separately, against the contracts and not the bodies, and in
    inference; boolean refinements (Examples/Flags.v), with the
    counter-models of their booleans; the answer [Undecided] of
    inference, with an oracle that never answers and with a qualifier
    outside the difference fragment.  The last group is not a
    computation: the hypothesis on the oracle of the open contracts of
    weakening is not contradictory, while completeness on every
    obligation would be; it uses classical axioms, here only. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Obligation.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Solver Require Import Diff Elim Prove.
From Liquid.Refine Require Import Spec Wp Check Measure.
From Liquid.Liquid Require Import Weaken Template Infer.
From Liquid.Examples Require Import Bounded Inc Calls Sum Loop Append Flags.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition failed {C} (r : ianswer C) : bool := match r with IFailed _ => true | _ => false end.
Definition inferred {C} (r : ianswer C) : bool := match r with Inferred _ _ _ => true | _ => false end.
Definition is_err {A} (r : result string A) : bool := match r with Err _ => true | Ok _ => false end.

Definition kinds {C} (vs : list (verdict C)) : list string :=
  map (fun v => match v with Proved _ => "Proved" | Refuted _ => "Refuted" | Unknown _ => "Unknown" end) vs.

(** The kinds of the verdicts of a report. *)
Definition verdicts {C} (r : result string (list (obligation * verdict C))) : result string (list string) :=
  match r with Ok l => Ok (kinds (map snd l)) | Err e => Err e end.

(** The counter-models of a report, each with its check on its
    obligation. *)
Definition models {C} (r : result string (list (obligation * verdict C))) : list (cmodel * bool) :=
  match r with
  | Ok l => flat_map (fun p => match snd p with Refuted m => [(m, check_counter m (fst p))] | _ => [] end) l
  | Err _ => []
  end.

Definition solution_of {C} (r : ianswer C) : option solution :=
  match r with Inferred _ sol _ => Some sol | _ => None end.

(** The qualifiers removed by weakening, in order. *)
Definition removed (log : list wevent) : list formula :=
  flat_map (fun e => match e with WStep _ _ rem _ => map (fun r => fst (fst r)) rem | WRound _ => [] end) log.

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

(** ** The elimination of equalities and lists (stage 8) *)

(** Two calls [f 0]: [d = r₁ − r₂] eliminated, [r₁ = r₂] refuted by a
    model that no run reaches. *)
Example two_calls_refuted :
  kinds (map prove (client_obligations RuleName bounded bounded_spec client_twice))
  = ["Proved"; "Proved"; "Refuted"].
Proof. vm_compute. reflexivity. Qed.

(** The obligation of the branch [cons] of [append]. *)
Definition cons_ob : obligation :=
  mkOb (LResult "append")
       [FEq (TLen "xs") (TAdd (TConst 1) (TLen "t")); FEq (TLen "r") (TAdd (TLen "t") (TLen "ys"));
        FEq (TLen "z") (TAdd (TConst 1) (TLen "r"))]
       (FEq (TLen "z") (TAdd (TLen "xs") (TLen "ys"))).

(** Without the steps, the certificate [0 = 0] does not check; with the
    steps the solver found, it does. *)
Example cons_needs_steps : check_cert cons_ob (mkCert [] [CertTrivial; CertTrivial]) = false.
Proof. vm_compute. reflexivity. Qed.

Example cons_steps : check_cert cons_ob (mkCert (elims_of cons_ob) [CertTrivial; CertTrivial]) = true.
Proof. vm_compute. reflexivity. Qed.

(** A forged step: [len r := len t], which no hypothesis gives. *)
Example forged_step :
  check_cert cons_ob (mkCert [(NLen "r", TLen "t")] [CertTrivial; CertTrivial]) = false.
Proof. vm_compute. reflexivity. Qed.

(** An equality with no coefficient [±1] is not eliminated: [2·d = 3·y];
    in [2·d = y] the variable [y] is. *)
Example no_unit_coefficient :
  elims_of (mkOb (LResult "c") [FEq (TMul 2 (TVar "d")) (TMul 3 (TVar "y"))] (FLt (TConst 0) (TVar "d"))) = [].
Proof. vm_compute. reflexivity. Qed.

Example unit_coefficient :
  elims_of (mkOb (LResult "c") [FEq (TMul 2 (TVar "d")) (TVar "y")] (FLt (TConst 0) (TVar "d")))
  = [(NInt "y", TMul 2 (TVar "d"))].
Proof. vm_compute. reflexivity. Qed.

(** [match] on an integer, and a head and a tail of the same name, are
    errors of typing. *)
Example match_on_int :
  is_err (ty_expr [] [("x", TyInt)] (lmatch "x" (ERet (num 0)) "h" "t" (ERet (num 1)))) = true.
Proof. vm_compute. reflexivity. Qed.

Example match_same_names :
  is_err (ty_expr [] [("x", TyList)] (lmatch "x" (ERet (num 0)) "h" "h" (ERet (num 1)))) = true.
Proof. vm_compute. reflexivity. Qed.

(** A measure over a list parameter is in scope; over the local [t] it
    is not. *)
Example measure_list_local :
  is_err (check_measures prove append_prog append_spec [("append", TLen "t")]) = true.
Proof. vm_compute. reflexivity. Qed.

(** [len ys] does not decrease. *)
Example measure_list_ys : accepted (check_measures prove append_prog append_spec [("append", TLen "ys")]) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Reserved names *)

(** A client may not bind a copy [r.x] of [RuleRoot]: assuming
    [r.x = −1], [let r = inc 0 in r] would be accepted with [ν = 0],
    although it returns [1]. *)
Definition client_copy_name : client :=
  mkClient [("r.x", TyInt)] [FEq (TVar "r.x") (TConst (-1))] (lcall "r" "inc" [num 0] (ERet "r"))
           (FEq (TVar nu) (TConst 0)).

Example copy_name_refused :
  check_client_with prove RuleRoot inc_prog inc_spec client_copy_name = Err "the variables of the client".
Proof. vm_compute. reflexivity. Qed.

(** Nor a program, by [let] or as a parameter. *)
Example copy_name_let : ty_expr [] [("x", TyInt)] (ladd "r.x" "x" (num 1) (ERet "r.x")) = Err "name not fresh: r.x".
Proof. vm_compute. reflexivity. Qed.

Example copy_name_param : ty_prog [mkFun "g" [("a.b", TyInt)] TyInt (ERet "a.b")] = Err "reserved parameter in g".
Proof. vm_compute. reflexivity. Qed.

(** ** Clients checked separately

    A client is checked against the contracts of the program, not its
    bodies: its obligations are the preconditions of its calls and its
    property [ψ] under [φ]. *)

(** [f 1 + 2]: the call and the result; the body of [f] is not among
    them.  [f 2] fails at the call, used or not. *)
Example client_f1_verdicts : verdicts (check_client prove bounded bounded_spec client_f1) = Ok ["Proved"; "Proved"].
Proof. vm_compute. reflexivity. Qed.

Example client_f2_verdicts : verdicts (check_client prove bounded bounded_spec client_f2) = Ok ["Refuted"; "Proved"].
Proof. vm_compute. reflexivity. Qed.

Example client_f2_dropped_verdicts :
  verdicts (check_client prove bounded bounded_spec client_f2_dropped) = Ok ["Refuted"].
Proof. vm_compute. reflexivity. Qed.

(** With the body [3], [f 1 + 2] returns [5], but the contract of [f]
    allows the result [0], and [ν = 5] is refuted by [r = 0]: a client
    sees the contract only. *)
Definition client_f1_exact : client := mkClient [] [] (cl_expr client_f1) (FEq (TVar nu) (TConst 5)).

Example client_f1_exact_runs : evalFuel 10 bounded3 [] (cl_expr client_f1_exact) = Value (VInt 5).
Proof. vm_compute. reflexivity. Qed.

Example client_f1_exact_refuted :
  models (check_client prove bounded3 bounded_spec client_f1_exact) = [(mkCModel [("r", 0%Z); ("s", 2%Z)] [] [], true)].
Proof. vm_compute. reflexivity. Qed.

(** The hypotheses [φ] of exercise 1 are needed: without [x < y] the
    difference [y − x] may be [0]. *)
Definition client_ex1_no_hyp : client :=
  mkClient (cl_env client_ex1) [FLe (TConst 0) (TVar "x")] (cl_expr client_ex1) (cl_post client_ex1).

Example client_ex1_hyp_needed :
  models (check_client prove [] [] client_ex1_no_hyp) = [(mkCModel [("d", 0%Z); ("x", 0%Z)] [] [], true)].
Proof. vm_compute. reflexivity. Qed.

(** Malformed clients are refused before any obligation: two variables
    of one name; [φ] over a name not bound; [ψ] reading a boolean result
    as an integer; an unknown in the first algorithm; a call of a
    function the program does not define; a [let] rebinding a variable
    of the client. *)
Example client_duplicate_variable :
  check_client prove bounded bounded_spec (mkClient [("x", TyInt); ("x", TyInt)] [] (ERet "x") ftrue)
  = Err "the variables of the client".
Proof. vm_compute. reflexivity. Qed.

Example client_out_of_scope :
  check_client prove bounded bounded_spec (mkClient [] [FLe (TConst 0) (TVar "y")] (ERet (num 0)) ftrue)
  = Err "the refinements of the client: scope or sorts".
Proof. vm_compute. reflexivity. Qed.

Example client_wrong_sort :
  check_client prove flags_prog flags_spec (mkClient [] [] (lcall "b" "yes" [num 1] (ERet "b")) (FLe (TConst 0) (TVar nu)))
  = Err "the refinements of the client: scope or sorts".
Proof. vm_compute. reflexivity. Qed.

Example client_with_unknown :
  check_client prove bounded bounded_spec (mkClient [] [FKappa "κ" []] (ERet (num 0)) ftrue)
  = Err "the refinements of the client: scope or sorts".
Proof. vm_compute. reflexivity. Qed.

Example client_unknown_function :
  check_client prove bounded bounded_spec (mkClient [] [] (lcall "r" "g" [] (ERet "r")) ftrue) = Err "unknown function g".
Proof. vm_compute. reflexivity. Qed.

Example client_rebinds :
  check_client prove bounded bounded_spec (mkClient [("r", TyInt)] [] (lcall "r" "f" [num 1] (ERet "r")) ftrue)
  = Err "name not fresh: r".
Proof. vm_compute. reflexivity. Qed.

(** In inference a client gives constraints like a body, and comes
    first: [go a n n] removes [i < n] and [i = 0]; the invariant is
    found all the same, and the client is checked again with it. *)
Example infer_client_go :
  match infer prove sum_prog (sum_tspec quals) [client_go_n] with
  | (log, Inferred S' sol _) =>
      Some (removed log, sol, accepted (check_client prove sum_prog S' client_go_n))
  | _ => None
  end
  = Some ([FLt (TVar "i") (TVar "n"); FEq (TVar "i") (TConst 0)],
          [(kappa_name, [FLe (TConst 0) (TVar "i"); FLe (TVar "i") (TVar "n")])], true).
Proof. vm_compute. reflexivity. Qed.

(** A property [ψ] of a client that no solution gives: [go] promises
    nothing of its result, and [ν = 0] is refuted at the client. *)
Definition client_go_0 : client := mkClient (cl_env client_go_n) (cl_pre client_go_n) (cl_expr client_go_n) (FEq (TVar nu) (TConst 0)).

Example infer_client_refuted :
  match snd (infer prove sum_prog (sum_tspec quals) [client_go_0]) with
  | IRefuted ob m => Some (ob_label ob, check_counter m ob)
  | _ => None
  end = Some (LResult client_scope, true).
Proof. vm_compute. reflexivity. Qed.

(** ** Boolean refinements (Examples/Flags.v) *)

Example flags_accepted : accepted (check_prog prove flags_prog flags_spec) = true.
Proof. vm_compute. reflexivity. Qed.

(** [¬ν] for [yes] is refuted by [x = 1]; [choose] without its
    precondition by [b] false. *)
Example flags_yes_wrong :
  models (check_prog prove flags_prog flags_spec_yes_wrong) = [(mkCModel [("x", 1%Z)] [] [], true)].
Proof. vm_compute. reflexivity. Qed.

Example flags_no_flag :
  models (check_prog prove flags_prog flags_spec_no_flag) = [(mkCModel [("x", (-1)%Z)] [("b", false)] [], true)].
Proof. vm_compute. reflexivity. Qed.

Example flags_clients :
  map (fun cl => verdicts (check_client prove flags_prog flags_spec cl))
      [client_yes; client_yes0; client_choose; client_choose_false; client_branch; client_branch_not]
  = [Ok ["Proved"; "Proved"; "Proved"]; Ok ["Refuted"]; Ok ["Proved"]; Ok ["Refuted"];
     Ok ["Refuted"; "Proved"]; Ok ["Proved"; "Proved"]].
Proof. vm_compute. reflexivity. Qed.

(** The model of [client_branch] sets [b] to [true], not the default
    [false]. *)
Example flags_branch_model :
  models (check_client prove flags_prog flags_spec client_branch) = [(mkCModel [] [("b", true)] [], true)].
Proof. vm_compute. reflexivity. Qed.

Example flags_client_runs : evalFuel 10 flags_prog [] (cl_expr client_yes) = Value (VInt 1).
Proof. vm_compute. reflexivity. Qed.

(** The unknowns over booleans: the precondition of [choose] comes from
    its client, [b] for [choose true 5], [¬b] for [choose false 5], with
    the postcondition of the live branch; with no client it stays the
    strongest. *)
Example flags_inferred :
  solution_of (snd (infer prove flags_prog flags_tspec [client_yes; client_choose]))
  = Some [("κy", [bvar nu]); ("κb", [bvar "b"]); ("κr", [FEq (TVar nu) (TVar "x")])].
Proof. vm_compute. reflexivity. Qed.

Example flags_inferred_false :
  solution_of (snd (infer prove flags_prog flags_tspec [client_choose_false]))
  = Some [("κy", [bvar nu]); ("κb", [FNot (bvar "b")]); ("κr", [FLe (TConst 0) (TVar nu); FEq (TVar nu) (TConst 0)])].
Proof. vm_compute. reflexivity. Qed.

Example flags_inferred_alone :
  solution_of (snd (infer prove flags_prog flags_tspec []))
  = Some [("κy", [bvar nu]); ("κb", [bvar "b"; FNot (bvar "b")]);
          ("κr", [FLe (TConst 0) (TVar nu); FEq (TVar nu) (TVar "x"); FEq (TVar nu) (TConst 0)])].
Proof. vm_compute. reflexivity. Qed.

(** ** The answer Undecided

    Weakening stops at the first [Unknown]: it neither keeps the
    qualifier, which may be false, nor removes it, which needs a
    counter-model. *)

Definition no_answer (ob : obligation) : verdict unit := Unknown "no answer".

(** The first query, before any removal. *)
Example undecided_first_query :
  match infer no_answer sum_prog (sum_tspec quals) [] with
  | (log, IUndecided ob why) => Some (log, ob_label ob, why)
  | _ => None
  end = Some ([WRound 1], LPre "sum" "go" "s", "no answer").
Proof. vm_compute. reflexivity. Qed.

(** [Unknown] is not acceptance: with the same oracle the first
    algorithm rejects [sum], which [prove] accepts. *)
Example undecided_not_accepted : accepted (check_prog no_answer sum_prog sum_spec) = false.
Proof. vm_compute. reflexivity. Qed.

(** With the difference solver, [0 ≤ i + n] (Examples/Sum.v): two
    removals by counter-models, then [0 ≤ j + n] at the recursive call
    in the second round, once [i = 0] is gone. *)
Example undecided_outside :
  match infer prove sum_prog (sum_tspec quals_outside) [] with
  | (log, IUndecided ob _) => Some (removed log, ob_label ob, ob_goal ob)
  | _ => None
  end = Some ([FLt (TVar "i") (TVar "n"); FEq (TVar "i") (TConst 0)], LPre "go" "go" "s",
              FLe (TConst 0) (TAdd (TVar "j") (TVar "n"))).
Proof. vm_compute. reflexivity. Qed.

Example unknown_outside : verdicts (check_prog prove sum_prog sum_spec_outside) = Ok ["Proved"; "Proved"; "Unknown"].
Proof. vm_compute. reflexivity. Qed.

(** ** The hypothesis of the open contracts of weakening *)

(** An oracle that answers every obligation is unsound: [⊢ ¬κ()] is not
    valid ([κ] read as true falsifies it) and has no counter-model ([κ]
    read as false).  Hence [oracle_complete] asks for an answer only on
    the obligations without unknowns. *)
Lemma complete_everywhere_unsound : forall C (o : obligation -> verdict C),
  oracle_sound o -> ~ (forall ob why, o ob <> Unknown why).
Proof.
  intros C o Hs Hc. set (ob := mkOb (LResult "f") [] (FNot (FKappa "k" []))).
  specialize (Hs ob). destruct (o ob) as [c | m | why] eqn:E; cbn in Hs.
  - exact (Hs (fun _ _ => true) (mkVal (fun _ => 0%Z) (fun _ => false) (fun _ => 0%Z))
              (fun _ => Z.le_refl 0) (Forall_nil _) eq_refl).
  - destruct Hs as (_ & _ & Hg). apply Hg. intros H. exact (Bool.diff_false_true H).
  - exact (Hc ob why E).
Qed.

(** With classical logic there is a sound oracle complete on the
    obligations without unknowns: the hypotheses of [weaken_strongest]
    and [weaken_order_independent] are satisfiable, the contracts are not
    vacuous.  The axioms of ClassicalEpsilon are used here only; no
    contract of Contracts.v depends on this file. *)
From Stdlib Require Import ClassicalEpsilon.

Definition classical_oracle (ob : obligation) : verdict unit :=
  match excluded_middle_informative (exists m, falsifies (val_of_cmodel m) ob) with
  | left H => Refuted (proj1_sig (constructive_indefinite_description _ H))
  | right _ => if ob_kfree ob then Proved tt else Unknown "an obligation with unknowns"
  end.

Lemma classical_oracle_sound : oracle_sound classical_oracle.
Proof.
  intros ob. unfold verdict_sound, classical_oracle.
  destruct (excluded_middle_informative _) as [H | Hn].
  - exact (proj2_sig (constructive_indefinite_description _ H)).
  - destruct (ob_kfree ob) eqn:Ek; [ | exact I].
    intros ki ρ Hl Hh. apply NNPP. intros Hg. apply Hn.
    exists (restrict ρ ob). exact (kfree_refutable ki ρ ob Ek Hl Hh Hg).
Qed.

Lemma classical_oracle_complete : oracle_complete classical_oracle.
Proof.
  intros ob why Hk. unfold classical_oracle.
  destruct (excluded_middle_informative _); [discriminate | rewrite Hk; discriminate].
Qed.

Lemma restricted_completeness_satisfiable :
  exists o : obligation -> verdict unit, oracle_sound o /\ oracle_complete o.
Proof. exists classical_oracle. exact (conj classical_oracle_sound classical_oracle_complete). Qed.
