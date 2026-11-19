(** * Contracts of lecture 9: refinement contracts and Liquid inference

    The guarantees of the development, stated as [Prop] definitions so
    that their exact form is kernel-checked independently of their
    proofs.  A contract followed by a theorem [..._holds] is proved; one
    without a theorem is an open obligation, stated precisely but not
    proved.  None of the proved contracts rests on an axiom:
    checks/Assumptions.v prints their assumptions, and [make assumptions]
    fails otherwise.

    The readiness levels of the plan:
    1. an executable artifact: both algorithms, the extraction with exact
       integers, the demonstrations 1–4, the regressions and the native
       reference compared with the extract: reached;
    2. proved, without axioms: the certificates of the difference solver,
       the soundness of [prove], [gen] as the unfolding of [wp], the
       contracts of the primitives, the operational guarantee of the first
       algorithm with recursive contracts, the termination of weakening
       within its fuel, and the result of inference accepted by the first
       algorithm: reached;
    3. open: the completeness of the solver on its fragment, the strongest
       solution of weakening and its independence of the order of the
       constraints, and termination from the obligations of measure.

    The second algorithm is not in the trusted base: [Inferred] is
    returned only after the first algorithm accepted the contracts it
    found ([infer_rechecked]), and the operational guarantee applies to
    them as to any accepted contracts.  The solver is not trusted either:
    its answers carry certificates checked by [check_cert] and
    [check_counter], proved sound.

    Trusted beyond the Rocq kernel: the extraction to OCaml, with the
    integers as Zarith integers and strings as OCaml strings
    (extraction/Extract.v); the OCaml printer and demonstrations.  The
    hand-written reference in reference/ is not covered by these proofs;
    the differential test compares it with the extract. *)

From Stdlib Require Import String List Bool ZArith Permutation.
Import ListNotations.
From Liquid.Common Require Import Result Traced.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Solver Require Import Diff Linear Prove.
From Liquid.Lang Require Import Syntax Typing Eval EvalFacts.
From Liquid.Refine Require Import Spec Wp Gen Check Sound Measure.
From Liquid.Liquid Require Import Horn Weaken Template Infer.
From Liquid.Examples Require Import Sum Loop.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** The difference solver (stage 3) *)

(** A model is checked against every edge of the graph. *)
Definition model_certificate_sound : Prop :=
  forall G m, check_model G m = true -> models (val_of m) G.

Theorem model_certificate_sound_holds : model_certificate_sound.
Proof. exact check_model_sound. Qed.

(** A checked cycle of positive weight excludes every model. *)
Definition cycle_certificate_sound : Prop :=
  forall G c, cycle_ok G c = true -> forall v, ~ models v G.

Theorem cycle_certificate_sound_holds : cycle_certificate_sound.
Proof. exact cycle_ok_sound. Qed.

(** A cycle of the graph with the negation of an edge entails the edge. *)
Definition entailment_certificate_sound : Prop :=
  forall G e c, entailment_ok G e c = true -> forall v, models v G -> edge_sat v e.

Theorem entailment_certificate_sound_holds : entailment_certificate_sound.
Proof. exact entailment_ok_sound. Qed.

(** The certificate of [Proved] makes the obligation valid. *)
Definition proof_certificate_sound : Prop :=
  forall ob c, check_cert ob c = true -> valid ob.

Theorem proof_certificate_sound_holds : proof_certificate_sound.
Proof. exact check_cert_sound. Qed.

(** A checked counter-model satisfies the hypotheses and violates the
    goal. *)
Definition counter_model_sound : Prop :=
  forall m ob, check_counter m ob = true -> falsifies (val_of_cmodel m) ob.

Theorem counter_model_sound_holds : counter_model_sound.
Proof. exact check_counter_sound. Qed.

(** [Proved] implies validity, [Refuted] gives a falsifying valuation. *)
Definition solver_sound : Prop := oracle_sound prove.

Theorem solver_sound_holds : solver_sound.
Proof. exact prove_sound. Qed.

(** An obligation of the fragment: every hypothesis and the goal split
    into difference constraints, constants and boolean atoms, nothing
    outside ([dropped] is then empty). *)
Definition in_fragment (ob : obligation) : Prop :=
  Forall (fun a => is_out a = false) (hyp_atoms ob ++ goal_atoms ob).

(** Open: on its fragment the solver decides, it does not answer
    [Unknown]; with [solver_sound], [Proved] iff valid. *)
Definition solver_complete : Prop :=
  forall ob, in_fragment ob -> forall why, prove ob <> Unknown why.

(** ** The language (stage 1) *)

(** A typed program fails only by a read out of bounds. *)
Definition evaluation_typed : Prop :=
  forall k P ρ Γ e T, ty_prog P = Ok tt -> env_ok ρ Γ -> ty_expr P Γ e = Ok T ->
    typed_answer (evalFuel k P ρ e) T.

Theorem evaluation_typed_holds : evaluation_typed.
Proof. exact eval_typed. Qed.

(** More fuel keeps a value. *)
Definition fuel_monotone : Prop :=
  forall k k' P ρ e v, (k <= k')%nat -> evalFuel k P ρ e = Value v -> evalFuel k' P ρ e = Value v.

Theorem fuel_monotone_holds : fuel_monotone.
Proof. exact evalFuel_value_mono. Qed.

(** ** Algorithm 1: [wp], [gen] and the guarantee (stages 4, 5) *)

(** The generator is the unfolding of [wp] into flat obligations. *)
Definition gen_flattens_wp : Prop :=
  forall rule P S scope Γ φ e ψ, gen rule P S scope Γ φ e ψ = flatten φ (wp rule P S scope Γ e ψ).

Theorem gen_flattens_wp_holds : gen_flattens_wp.
Proof. intros rule P S scope. exact (gen_flatten rule P S scope). Qed.

(** The contracts of the primitives agree with their semantics: on typed
    arguments the precondition excludes [Stuck], and the result satisfies
    the postcondition. *)
Definition primitives_sound : Prop :=
  forall p vs ρp,
    Forall2 has_ty vs (fst (prim_sig p)) -> bind_params (prim_params p) vs = Some ρp ->
    Forall (hold ρp) (c_pre (prim_contract p)) ->
    exists v, eval_prim p vs = Ok v /\ has_ty v (snd (prim_sig p)) /\ hold ((nu, v) :: ρp) (c_post (prim_contract p)).

Theorem primitives_sound_holds : primitives_sound.
Proof. exact prim_spec_sound. Qed.

(** The operational guarantee: for every fuel, a function of an accepted
    program run on arguments satisfying its precondition answers
    [Timeout] or a value satisfying its postcondition, never [Stuck].
    Termination is not assumed. *)
Definition check_prog_guarantee : Prop :=
  forall C (oracle : obligation -> verdict C) P S,
    oracle_sound oracle -> accepted (check_prog oracle P S) = true ->
    forall k fd vs ρf, In fd P -> bind_params (fd_params fd) vs = Some ρf ->
      Forall2 has_ty vs (map snd (fd_params fd)) ->
      Forall (hold ρf) (c_pre (contract_of S fd)) ->
      answer_ok (evalFuel k P ρf (fd_body fd)) ρf (c_post (contract_of S fd)).

Theorem check_prog_guarantee_holds : check_prog_guarantee.
Proof. intros C oracle P S. exact (check_prog_sound oracle P S). Qed.

(** The same for a client, in every environment of its types that
    satisfies [φ], against [ψ]. *)
Definition check_client_guarantee : Prop :=
  forall C (oracle : obligation -> verdict C) P S cl,
    oracle_sound oracle -> accepted (check_prog oracle P S) = true -> accepted (check_client oracle P S cl) = true ->
    forall ρ, env_ok ρ (cl_env cl) -> Forall (hold ρ) (cl_pre cl) ->
    forall k, answer_ok (evalFuel k P ρ (cl_expr cl)) ρ (cl_post cl).

Theorem check_client_guarantee_holds : check_client_guarantee.
Proof. intros C oracle P S cl. exact (check_client_sound oracle P S cl). Qed.

(** ** Algorithm 2: Liquid inference (stage 6) *)

(** The normalization of obligations into constraints keeps their
    meaning. *)
Definition normalize_sound : Prop :=
  forall ki ρ ob, ob_holds ki ρ ob <-> Forall (ob_holds ki ρ) (normalize ob).

Theorem normalize_sound_holds : normalize_sound.
Proof. exact normalize_holds. Qed.

(** Templates are turned into contracts whole: distinct names, each of a
    function of the program, with exactly one refinement per parameter;
    nothing is dropped. *)
Definition instantiate_whole : Prop :=
  forall P T S D, instantiate P T = Ok (S, D) ->
    distinct (map fst T) = true /\
    Forall2 (fun e se => fst se = fst e /\
               exists fd, find_fun (fst e) P = Some fd /\
                          length (ct_pre (snd e)) = length (fd_params fd) /\
                          length (c_pre (snd se)) = length (fd_params fd)) T S.

Theorem instantiate_whole_holds : instantiate_whole.
Proof. exact instantiate_complete. Qed.

(** Weakening ends within its fuel [1 + Σ|Qκ|]. *)
Definition weaken_terminates : Prop :=
  forall C (oracle : obligation -> verdict C) D hs log log' e,
    weaken oracle D hs log = (log', Err e) -> e <> WOutOfFuel.

Theorem weaken_terminates_holds : weaken_terminates.
Proof. intros C oracle D. exact (weaken_fuel_enough oracle D). Qed.

(** The contracts found are accepted by the first algorithm, for the
    definitions and for every client: the guarantee applies to them. *)
Definition infer_rechecked : Prop :=
  forall C (oracle : obligation -> verdict C) P T cls log S' sol rep,
    infer oracle P T cls = (log, Inferred S' sol rep) ->
    exists D S,
      instantiate P T = Ok (S, D) /\ S' = apply_spec D sol S /\
      accepted (check_prog oracle P S') = true /\
      Forall (fun cl => accepted (check_client oracle P S' cl) = true) (map (apply_client D sol) cls).

Theorem infer_rechecked_holds : infer_rechecked.
Proof. intros C oracle. exact (infer_checked oracle). Qed.

(** *** Open: the strongest solution *)

(** An oracle that never answers [Unknown]; with soundness it decides
    validity. *)
Definition oracle_complete {C} (oracle : obligation -> verdict C) : Prop :=
  forall ob why, oracle ob <> Unknown why.

Fixpoint fkappas (p : formula) : list string :=
  match p with
  | FKappa k _ => [k]
  | FAnd p q | FOr p q => fkappas p ++ fkappas q
  | FNot p => fkappas p
  | _ => []
  end.

(** A constraint of the shape [horn_of] gives, over the unknowns of [D]:
    an unknown is a whole hypothesis or the whole goal. *)
Definition horn_ok (D : list kdecl) (h : horn) : Prop :=
  forallb hyp_shape_ok (h_hyps h) = true /\
  (match h_goal h with HFixed p => kfree p = true | HKappa _ _ => True end) /\
  Forall (fun k => In k (map kd_name D)) (flat_map fkappas (hgoal_formula (h_goal h) :: h_hyps h)).

(** A solution in [Q]: every unknown keeps some of its qualifiers. *)
Definition within (D : list kdecl) (sol : solution) : Prop :=
  forall d, In d D -> exists qs, assoc (kd_name d) sol = Some qs /\ incl qs (kd_quals d).

(** [sol] keeps every qualifier [sol'] keeps. *)
Definition stronger (D : list kdecl) (sol sol' : solution) : Prop :=
  forall d qs qs', In d D -> assoc (kd_name d) sol = Some qs -> assoc (kd_name d) sol' = Some qs' -> incl qs' qs.

(** The obligation of a constraint under a solution. *)
Definition horn_under (D : list kdecl) (sol : solution) (h : horn) : obligation :=
  mkOb (h_label h) (map (apply_sol D sol) (h_hyps h)) (apply_sol D sol (hgoal_formula (h_goal h))).

Definition solves (D : list kdecl) (hs : list horn) (sol : solution) : Prop :=
  Forall (fun h => valid (horn_under D sol h)) hs.

(** Open: with a sound and complete oracle, weakening returns the
    strongest solution in [Q], or a refutation when [Q] has none. *)
Definition weaken_strongest : Prop :=
  forall C (oracle : obligation -> verdict C) D hs,
    oracle_sound oracle -> oracle_complete oracle -> kdecls_ok D = true -> Forall (horn_ok D) hs ->
    match snd (run_traced (weaken oracle D hs)) with
    | Ok sol => within D sol /\ solves D hs sol /\
                forall sol', within D sol' -> solves D hs sol' -> stronger D sol sol'
    | Err (WRefuted _ _) => forall sol', within D sol' -> ~ solves D hs sol'
    | Err _ => False
    end.

(** Open: with such an oracle, the answer does not depend on the order
    of the constraints; the traces may. *)
Definition weaken_order_independent : Prop :=
  forall C (oracle : obligation -> verdict C) D hs hs',
    oracle_sound oracle -> oracle_complete oracle -> kdecls_ok D = true -> Forall (horn_ok D) hs ->
    Permutation hs hs' ->
    match snd (run_traced (weaken oracle D hs)), snd (run_traced (weaken oracle D hs')) with
    | Ok sol, Ok sol' => stronger D sol sol' /\ stronger D sol' sol
    | Err (WRefuted _ _), Err (WRefuted _ _) => True
    | _, _ => False
    end.

(** ** Termination (stage 7) *)

(** Every measure is checked: none of a function the program does not
    define, none twice, and all its obligations proved. *)
Definition measures_whole : Prop :=
  forall C (oracle : obligation -> verdict C) P S M,
    accepted (check_measures oracle P S M) = true ->
    distinct (map fst M) = true /\
    Forall (fun m => exists fd, find_fun (fst m) P = Some fd) M /\
    forall ob, In ob (measure_obligations P S M) -> is_proved (oracle ob) = true.

Theorem measures_whole_holds : measures_whole.
Proof. intros C oracle. exact (check_measures_complete oracle). Qed.

(** [sum] returns the sum of the array with the fuel [4·len a + 4]. *)
Definition sum_runs : Prop :=
  forall l k, (4 * length l + 4 <= k)%nat -> run_fun k sum_prog "sum" [VArr l] = Value (VInt (zsum l)).

Theorem sum_runs_holds : sum_runs.
Proof. exact sum_fuel. Qed.

(** [sum] never reads out of bounds, the guarantee applied to its
    accepted contracts. *)
Definition sum_safe : Prop :=
  forall l k why, run_fun k sum_prog "sum" [VArr l] <> Stuck why.

Theorem sum_safe_holds : sum_safe.
Proof. exact sum_never_stuck. Qed.

(** [loop] and its client time out for every fuel. *)
Definition loop_times_out : Prop :=
  (forall k v, run_fun k loop_prog "loop" [v] = Timeout) /\
  (forall ρ, diverges loop_prog ρ (cl_expr client_loop)).

Theorem loop_times_out_holds : loop_times_out.
Proof. exact (conj loop_diverges client_loop_diverges). Qed.

(** [loop] is accepted with the postcondition [false] and has no measure. *)
Definition loop_unmeasured : Prop :=
  accepted (check_prog prove loop_prog loop_spec) = true /\
  forall C (oracle : obligation -> verdict C) μ,
    oracle_sound oracle -> accepted (check_measures oracle loop_prog loop_spec [("loop", μ)]) = false.

Theorem loop_unmeasured_holds : loop_unmeasured.
Proof. split; [vm_compute; reflexivity | exact loop_no_measure]. Qed.

(** Open: proved obligations of measure for the recursive functions and
    an order of the other calls imply termination on every input that
    satisfies the preconditions (Refine/Measure.v). *)
Definition measures_imply_termination : Prop := measures_terminate.
