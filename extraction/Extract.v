(** * Extraction driver

    Exports into generated/liquid.ml the evaluator, the logic, the
    difference solver, both algorithms, the examples of the lecture and
    the inputs of the tests of booleans (Examples/Flags.v).

    The integers of the programs, the valuations, the coefficients of
    linear forms and the weights of the graph, the checks of the
    certificates included, are the exact integers of Zarith
    (ExtrOcamlZBigInt), not the machine [int]: a replacement would not
    keep the semantics of ℤ.  Natural numbers (fuel, rounds) are exact
    non-negative integers too (ExtrOcamlNatBigInt).  Names are OCaml
    strings.  The build links the library [zarith]. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Liquid.Common Require Import Result Traced.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Solver Require Import Diff Linear Elim Prove.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Wp Gen Check Measure.
From Liquid.Liquid Require Import Horn Weaken Template Infer.
From Liquid.Examples Require Import Bounded Inc Calls Sum Loop Append Flags.

Extraction Language OCaml.
Set Extraction Output Directory "generated".

Extraction "liquid.ml"
  (* Logic *)
  ftrue ffalse fand fconj conjuncts kfree teval beval pevalb fsubst ksubst val_of_cmodel
  check_counter is_proved
  (* Solver *)
  solve entails lin decomp graph_of dropped goal_atoms hyp_atoms check_cert prove
  reduce elims_of back_subst attempt
  (* Lang *)
  find_fun evalFuel run_fun ty_prog ty_expr prim_name nu
  (* Refine *)
  contract_of prim_contract prim_params pre_inst post_inst cond_formula wp flatten gen
  fun_obligations prog_obligations client_obligations
  check_prog check_client check_prog_with check_client_with accepted all_proved judge
  measure_obligations check_measures
  (* Liquid *)
  normalize horn_of to_horn weaken apply_sol instantiate apply_spec infer infer_obligations of_contract
  (* Examples *)
  bounded bounded3 bounded_spec client_f1 client_f2 client_f2_dropped f_def f3_def
  inc_prog inc_spec inc_contract client_inc0
  client_twice
  sum_prog sum_prog_le sum_spec sum_def go_def quals quals_no_lower sum_tspec go_template
  sum_measures go_measure sum_spec_lower zsum client_go_n quals_outside sum_spec_outside
  loop_prog loop_spec client_loop loop_measures
  append_prog append_def append_spec append_spec_swapped append_spec_wrong append_measures client_ex1
  flags_prog flags_spec flags_spec_yes_wrong flags_spec_no_flag flags_tspec
  client_yes client_yes0 client_choose client_choose_false client_branch client_branch_not.
