(** * Obligations and verdicts

    An obligation is a flat implication [H₁, …, Hₙ ⊢ g] with a label of
    origin.  Its free names are implicitly universally quantified: it is
    valid when every valuation in which the lengths of arrays are
    non-negative and the hypotheses hold satisfies the goal, whatever the
    interpretation of the unknowns [κ].

    The label records where an obligation comes from, in names only, so
    that this module stays independent of the programs: the result of a
    body or of a client against its refinement, the precondition of a
    callee (a function or a primitive) at a [let], and the two
    obligations of a measure.

    A solver answers [Proved] with a certificate, [Refuted] with a
    counter-model, or [Unknown] with a reason.  The algorithms take the
    solver as a parameter [oracle]; [oracle_sound] is the hypothesis of
    their theorems: [Proved] means valid, [Refuted] comes with a
    valuation that falsifies the obligation.  For the difference solver
    of Solver/ it is proved; an external solver would be trusted. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula Subst.

Local Open Scope Z_scope.

Inductive label : Type :=
| LResult (scope : string)
| LPre (scope callee x : string)
| LMeasureNonneg (scope : string)
| LMeasureDecr (scope x : string).

Definition label_eq_dec (l1 l2 : label) : {l1 = l2} + {l1 <> l2}.
Proof. decide equality; apply string_dec. Defined.

Record obligation : Type := mkOb {
  ob_label : label;
  ob_hyps : list formula;
  ob_goal : formula
}.

Definition lens_nonneg (ρ : valuation) : Prop := forall a, 0 <= vlen ρ a.

Definition ob_holds (ki : kinterp) (ρ : valuation) (ob : obligation) : Prop :=
  Forall (holds ki ρ) (ob_hyps ob) -> holds ki ρ (ob_goal ob).

Definition valid (ob : obligation) : Prop :=
  forall ki ρ, lens_nonneg ρ -> ob_holds ki ρ ob.

Definition falsifies (ρ : valuation) (ob : obligation) : Prop :=
  lens_nonneg ρ /\ Forall (holds no_kappa ρ) (ob_hyps ob) /\ ~ holds no_kappa ρ (ob_goal ob).

Lemma falsifies_not_valid : forall ρ ob, falsifies ρ ob -> ~ valid ob.
Proof. intros ρ ob (Hl & Hh & Hg) Hv. exact (Hg (Hv no_kappa ρ Hl Hh)). Qed.

Inductive verdict (C : Type) : Type :=
| Proved (c : C)
| Refuted (m : cmodel)
| Unknown (why : string).

Arguments Proved {C} _.
Arguments Refuted {C} _.
Arguments Unknown {C} _.

Definition is_proved {C} (v : verdict C) : bool :=
  match v with Proved _ => true | _ => false end.

Definition verdict_sound {C} (ob : obligation) (v : verdict C) : Prop :=
  match v with
  | Proved _ => valid ob
  | Refuted m => falsifies (val_of_cmodel m) ob
  | Unknown _ => True
  end.

Definition oracle_sound {C} (oracle : obligation -> verdict C) : Prop :=
  forall ob, verdict_sound ob (oracle ob).

Lemma oracle_proved : forall {C} (oracle : obligation -> verdict C) ob,
  oracle_sound oracle -> is_proved (oracle ob) = true -> valid ob.
Proof.
  intros C oracle ob Hs H. specialize (Hs ob). unfold verdict_sound in Hs.
  destruct (oracle ob); [exact Hs | discriminate H | discriminate H].
Qed.

(** Checking a counter-model on the obligation itself: the lengths are
    non-negative, every hypothesis holds and the goal fails, [κ] read as
    false. *)
Definition check_counter (m : cmodel) (ob : obligation) : bool :=
  forallb (fun p => 0 <=? snd p) (cm_len m)
  && forallb (pevalb no_kappa (val_of_cmodel m)) (ob_hyps ob)
  && negb (pevalb no_kappa (val_of_cmodel m) (ob_goal ob)).

Lemma check_counter_sound : forall m ob, check_counter m ob = true -> falsifies (val_of_cmodel m) ob.
Proof.
  intros m ob H. unfold check_counter in H.
  apply andb_prop in H as [H Hg]. apply andb_prop in H as [Hl Hh].
  split; [ | split].
  - intros a. cbn. rewrite forallb_forall in Hl.
    induction (cm_len m) as [|[b z] l IH]; cbn; [lia | ].
    destruct (String.eqb a b).
    + specialize (Hl (b, z) (or_introl eq_refl)). cbn in Hl. lia.
    + apply IH. intros x Hx. apply Hl. now right.
  - apply Forall_forall. intros p Hp. rewrite forallb_forall in Hh. apply pevalb_holds, Hh, Hp.
  - intros Hgoal. apply pevalb_holds in Hgoal. rewrite Hgoal in Hg. discriminate Hg.
Qed.

(** ** Obligations without unknowns

    On an obligation without unknowns the two answers of a sound oracle
    are exhaustive: a valuation that falsifies it, for any interpretation
    of the unknowns, kept on the names the obligation mentions, is a
    counter-model ([kfree_refutable]).  With an unknown it is not so:
    [⊢ ¬κ()] is not valid ([κ] read as true falsifies it) and has no
    counter-model (a counter-model reads [κ] as false), so a sound oracle
    can only answer [Unknown] on it. *)

Definition ob_kfree (ob : obligation) : bool := forallb kfree (ob_hyps ob) && kfree (ob_goal ob).

(** An oracle that answers every obligation without unknowns; with
    [oracle_sound] it decides their validity.  Weakening asks only such
    obligations (Liquid/Weaken.v, [weaken_kfree_queries]). *)
Definition oracle_complete {C} (oracle : obligation -> verdict C) : Prop :=
  forall ob why, ob_kfree ob = true -> oracle ob <> Unknown why.

Definition ob_formulas (ob : obligation) : list formula := ob_goal ob :: ob_hyps ob.

(** A valuation kept on the names of an obligation. *)
Definition restrict (ρ : valuation) (ob : obligation) : cmodel :=
  mkCModel (map (fun x => (x, vint ρ x)) (flat_map fvars (ob_formulas ob)))
           (map (fun b => (b, vbool ρ b)) (flat_map fbvars (ob_formulas ob)))
           (map (fun a => (a, vlen ρ a)) (flat_map flens (ob_formulas ob))).

Lemma assoc_map : forall {A} (f : string -> A) x xs,
  assoc x (map (fun y => (y, f y)) xs) = if memb x xs then Some (f x) else None.
Proof.
  intros A f x xs. induction xs as [|y xs IH]; [reflexivity | ].
  cbn. destruct (String.eqb x y) eqn:E; [apply String.eqb_eq in E; subst; reflexivity | exact IH].
Qed.

Lemma restrict_agree : forall ρ ob p, In p (ob_formulas ob) ->
  agree_on (fvars p) (fbvars p) (flens p) (val_of_cmodel (restrict ρ ob)) ρ.
Proof.
  intros ρ ob p Hp. unfold agree_on, val_of_cmodel, restrict. cbn [vint vbool vlen cm_int cm_bool cm_len].
  repeat split; intros x Hx; rewrite assoc_map;
    (replace (memb x _) with true; [reflexivity | symmetry; apply memb_In, in_flat_map; eauto]).
Qed.

Lemma kfree_refutable : forall ki ρ ob, ob_kfree ob = true -> lens_nonneg ρ ->
  Forall (holds ki ρ) (ob_hyps ob) -> ~ holds ki ρ (ob_goal ob) ->
  falsifies (val_of_cmodel (restrict ρ ob)) ob.
Proof.
  intros ki ρ ob Hk Hl Hh Hg. unfold ob_kfree in Hk. apply andb_prop in Hk as [Hkh Hkg].
  rewrite forallb_forall in Hkh. split; [ | split].
  - intros a. cbn [val_of_cmodel restrict vlen cm_len]. rewrite assoc_map. destruct (memb a _); [apply Hl | lia].
  - apply Forall_forall. intros p Hp.
    rewrite (holds_agree no_kappa _ ρ p (restrict_agree ρ ob p (or_intror Hp))).
    rewrite (holds_kfree no_kappa ki ρ p (Hkh p Hp)).
    exact (proj1 (Forall_forall _ _) Hh p Hp).
  - rewrite (holds_agree no_kappa _ ρ _ (restrict_agree ρ ob _ (or_introl eq_refl))).
    rewrite (holds_kfree no_kappa ki ρ _ Hkg). exact Hg.
Qed.
