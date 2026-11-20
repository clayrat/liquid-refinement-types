(** * The difference solver

    [prove ob] decides an obligation [H₁, …, Hₙ ⊢ g] in the difference
    fragment:

    - the hypotheses are split into constraints ([decomp]); an edge of
      the fragment goes into the graph, [false] gives the contradictory
      edge [0 + 1 ≤ 0], a piece outside the fragment is dropped
      ([dropped] lists them for the trace).  Dropping a hypothesis keeps
      the answer [Proved] sound, not complete;
    - the edges [0 ≤ len a] for every array and [0 ≤ b ≤ 1] for every
      boolean variable are added: they hold in every valuation the
      obligation quantifies over;
    - the goal is split the same way; for every inequality the solver
      looks for a cycle in the graph with its negation, for [false] a
      cycle in the graph itself;
    - [Proved] carries one cycle per inequality of the goal;
    - a model found by the graph is translated into a valuation and
      checked by [pevalb] on the original obligation ([check_counter]);
      [Refuted] is returned only if it satisfies all the hypotheses and
      violates the goal.  Otherwise a dropped hypothesis could give a
      false counter-model, and weakening would remove a qualifier by it;
    - anything else is [Unknown] with a reason.

    If the obligation as it is gets [Unknown], the solver eliminates the
    equalities among the hypotheses (Solver/Elim.v) and tries the reduced
    obligation the same way: a hypothesis [d = r₁ − r₂] or
    [len r = len t + len ys] is outside the fragment, but substituting it
    can bring the rest into it.  The elimination comes second so that the
    answers and certificates of obligations already in the fragment stay
    as they are; it changes only answers [Unknown].

    The certificate of [Proved] — the steps of elimination, if any, and
    the items — is checked by [check_cert], independently of how it was
    found: the checker checks and applies the steps itself.
    [check_cert_sound] proves that a checked certificate makes the
    obligation valid.  With [check_counter_sound]
    of Logic/Obligation.v this gives [prove_sound]: the difference solver
    is a sound oracle.  Its completeness on the fragment is an open
    obligation of Contracts.v. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula Obligation.
From Liquid.Solver Require Import Diff Linear Elim.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Inductive cert_item : Type :=
| CertTrivial                                 (** a constant conjunct, true *)
| CertCycle (goal : option edge) (c : list edge).
  (** a cycle of the graph with the negation of [goal]; of the graph
      alone for the goal [false] *)

(** The steps of elimination (Solver/Elim.v), then one item per
    conjunct of the reduced goal; without steps, the obligation as it
    is. *)
Record cert : Type := mkCert {
  cert_elim : list elim;
  cert_items : list cert_item
}.

(** ** The graph of an obligation *)

Definition hyp_atoms (ob : obligation) : list catom := flat_map (decomp true) (ob_hyps ob).
Definition goal_atoms (ob : obligation) : list catom := decomp true (ob_goal ob).

Definition hyp_edge (a : catom) : list edge :=
  match a with
  | CEdge e => [e]
  | CFalse => [(NZero, 1, NZero)]
  | _ => []
  end.

Definition goal_edge (a : catom) : list edge := match a with CEdge e => [e] | _ => [] end.

Definition side_edges (n : node) : list edge :=
  match n with
  | NBool b => [(NZero, 0, NBool b); (NBool b, -1, NZero)]
  | NLen a => [(NZero, 0, NLen a)]
  | _ => []
  end.

Definition graph_of (ob : obligation) : list edge :=
  let hs := flat_map hyp_edge (hyp_atoms ob) in
  let gs := flat_map goal_edge (goal_atoms ob) in
  flat_map side_edges (nodes (hs ++ gs)) ++ hs.

(** The hypotheses, or their pieces, outside the fragment. *)
Definition dropped (ob : obligation) : list formula :=
  flat_map (fun a => match a with COut p true => [p] | COut p false => [FNot p] | _ => [] end) (hyp_atoms ob).

(** ** Checking a certificate *)

Definition item_ok (G : list edge) (a : catom) (ci : cert_item) : bool :=
  match a, ci with
  | CTrue, CertTrivial => true
  | CFalse, CertCycle None c => cycle_ok G c
  | CEdge e, CertCycle (Some e') c => (if edge_eq_dec e e' then true else false) && entailment_ok G e c
  | _, _ => false
  end.

Fixpoint items_ok (G : list edge) (gs : list catom) (cs : list cert_item) : bool :=
  match gs, cs with
  | [], [] => true
  | a :: gs', ci :: cs' => item_ok G a ci && items_ok G gs' cs'
  | _, _ => false
  end.

Definition check_cert (ob : obligation) (c : cert) : bool :=
  match reduce (cert_elim c) ob with
  | Some ob' => items_ok (graph_of ob') (goal_atoms ob') (cert_items c)
  | None => false
  end.

Lemma side_edges_sat : forall ρ n, lens_nonneg ρ -> Forall (edge_sat (nval ρ)) (side_edges n).
Proof.
  intros ρ n Hl. destruct n as [ | x | b | a]; cbn; repeat constructor; unfold edge_sat; cbn.
  - destruct (vbool ρ b); lia.
  - destruct (vbool ρ b); lia.
  - specialize (Hl a). lia.
Qed.

Lemma graph_models : forall ki ρ ob, lens_nonneg ρ -> Forall (holds ki ρ) (ob_hyps ob) ->
  models (nval ρ) (graph_of ob).
Proof.
  intros ki ρ ob Hl Hh. unfold graph_of, models. apply Forall_app. split.
  - apply Forall_forall. intros e He. apply in_flat_map in He as (n & _ & He).
    exact (proj1 (Forall_forall _ _) (side_edges_sat ρ n Hl) e He).
  - apply Forall_forall. intros e He. apply in_flat_map in He as (a & Ha & He).
    unfold hyp_atoms in Ha. apply in_flat_map in Ha as (h & Hin & Ha).
    pose proof (proj1 (Forall_forall _ _) Hh h Hin) as Hhold.
    pose proof (proj2 (decomp_iff ki ρ true h) Hhold) as Hd.
    pose proof (proj1 (Forall_forall _ _) Hd a Ha) as Hc.
    destruct a; cbn in He, Hc; try contradiction.
    destruct He as [<- | []]. exact Hc.
Qed.

Lemma item_ok_sound : forall ki ρ G a ci, models (nval ρ) G -> item_ok G a ci = true -> csem ki ρ a.
Proof.
  intros ki ρ G a ci HG H. destruct a as [ | | e | p pos]; destruct ci as [ | [e' | ] c]; cbn in H |- *;
    try discriminate H; try exact I.
  - exact (cycle_ok_sound G c H (nval ρ) HG).
  - apply andb_prop in H as [He Hc]. destruct (edge_eq_dec e e'); [ | discriminate He].
    exact (entailment_ok_sound G e c Hc (nval ρ) HG).
Qed.

Lemma items_ok_sound : forall ki ρ G gs cs, models (nval ρ) G -> items_ok G gs cs = true ->
  Forall (csem ki ρ) gs.
Proof.
  intros ki ρ G gs. induction gs as [|a gs IH]; intros [|ci cs] HG H; cbn in H; try discriminate H.
  - constructor.
  - apply andb_prop in H as [H1 H2]. constructor; [eapply item_ok_sound; eauto | eapply IH; eauto].
Qed.

Lemma items_valid : forall ob cs, items_ok (graph_of ob) (goal_atoms ob) cs = true -> valid ob.
Proof.
  intros ob cs H ki ρ Hl Hh.
  pose proof (graph_models ki ρ ob Hl Hh) as HG.
  pose proof (items_ok_sound ki ρ _ _ _ HG H) as Hg.
  exact (proj1 (decomp_iff ki ρ true (ob_goal ob)) Hg).
Qed.

Theorem check_cert_sound : forall ob c, check_cert ob c = true -> valid ob.
Proof.
  intros ob c H. unfold check_cert in H.
  destruct (reduce (cert_elim c) ob) as [ob' | ] eqn:E; [ | discriminate H].
  exact (reduce_sound _ ob ob' E (items_valid ob' _ H)).
Qed.

(** ** Finding the certificate *)

Definition cmodel_of (m : model) : cmodel :=
  mkCModel (flat_map (fun p => match fst p with NInt x => [(x, snd p)] | _ => [] end) m)
           (flat_map (fun p => match fst p with NBool b => [(b, negb (Z.eqb (snd p) 0))] | _ => [] end) m)
           (flat_map (fun p => match fst p with NLen a => [(a, snd p)] | _ => [] end) m).

Inductive search : Type :=
| SCert (c : list cert_item)
| SCounter (m : model)
| SUnknown (why : string).

Definition goal_step (G : list edge) (a : catom) : search :=
  match a with
  | CTrue => SCert [CertTrivial]
  | CFalse =>
      match solve G with
      | GCycle c => SCert [CertCycle None c]
      | GModel m => SCounter m
      | GUnknown => SUnknown "the graph search did not certify its answer"
      end
  | CEdge e =>
      match entails G e with
      | Entailed c => SCert [CertCycle (Some e) c]
      | Countered m => SCounter m
      | EUnknown => SUnknown "the graph search did not certify its answer"
      end
  | COut _ _ => SUnknown "the goal is outside the difference fragment"
  end.

Fixpoint run_goals (G : list edge) (gs : list catom) : search :=
  match gs with
  | [] => SCert []
  | a :: gs' =>
      match goal_step G a with
      | SCert c => match run_goals G gs' with SCert cs => SCert (c ++ cs)%list | r => r end
      | r => r
      end
  end.

(** One attempt: the steps [els] applied, the reduced obligation
    decided; the certificate is checked, and the model, extended by the
    eliminated nodes, is checked on the original obligation. *)
Definition attempt (els : list elim) (ob : obligation) : verdict cert :=
  match reduce els ob with
  | None => Unknown "the elimination does not apply"
  | Some ob' =>
      match run_goals (graph_of ob') (goal_atoms ob') with
      | SCert cs =>
          let c := mkCert els cs in
          if check_cert ob c then Proved c else Unknown "the certificate does not check"
      | SCounter m =>
          let cm := back_subst els (cmodel_of m) in
          if check_counter cm ob then Refuted cm
          else Unknown "the model of the fragment does not falsify the obligation (a dropped hypothesis)"
      | SUnknown why => Unknown why
      end
  end.

(** The obligation as it is; if that gives no answer, after the
    elimination of equalities. *)
Definition prove (ob : obligation) : verdict cert :=
  match attempt [] ob with
  | Unknown why =>
      match elims_of ob with
      | [] => Unknown why
      | els =>
          match attempt els ob with
          | Unknown why' => Unknown ("after the elimination of equalities: " ++ why')
          | v => v
          end
      end
  | v => v
  end.

Lemma attempt_sound : forall els ob, verdict_sound ob (attempt els ob).
Proof.
  intros els ob. unfold verdict_sound, attempt.
  destruct (reduce els ob) as [ob' | ]; [ | exact I].
  destruct (run_goals (graph_of ob') (goal_atoms ob')) as [c | m | why]; [ | | exact I].
  - destruct (check_cert ob (mkCert els c)) eqn:E; [exact (check_cert_sound ob _ E) | exact I].
  - destruct (check_counter (back_subst els (cmodel_of m)) ob) eqn:E; [exact (check_counter_sound _ _ E) | exact I].
Qed.

Theorem prove_sound : oracle_sound prove.
Proof.
  intros ob. unfold prove.
  pose proof (attempt_sound [] ob) as H0.
  destruct (attempt [] ob) as [c | m | why]; [exact H0 | exact H0 | ].
  destruct (elims_of ob) as [|st els]; [exact I | ].
  pose proof (attempt_sound (st :: els) ob) as H1.
  destruct (attempt (st :: els) ob); [exact H1 | exact H1 | exact I].
Qed.
