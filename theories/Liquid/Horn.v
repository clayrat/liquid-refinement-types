(** * Horn constraints

    The obligations of the generator with unknowns [κ] in place of some
    refinements.  [normalize] first splits the conjunctions of the
    hypotheses and splits a conjunction in the goal into separate
    obligations, keeping the label of origin: for instance
    [H ⊢ n = len a ∧ n ≥ 0 ∧ κ(i,n)] becomes two obligations with a fixed
    goal and one [H ⊢ κ(i,n)].  Then [horn_of] checks the shape: a [κ]
    is allowed only as a whole conjunct of the hypotheses or as the whole
    goal, and the rest contains no unknowns.  An occurrence under a
    negation or a disjunction is rejected.  The refinements with
    conjuncts [κ] get this shape after normalization, not directly at
    the output of the generator.

    Independent of the programs (Lang/). *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Subst Obligation.

Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive hgoal : Type :=
| HKappa (k : string) (us : list arg)
| HFixed (p : formula).

Record horn : Type := mkHorn {
  h_label : label;
  h_hyps : list formula;
  h_goal : hgoal
}.

Definition hgoal_formula (g : hgoal) : formula :=
  match g with HKappa k us => FKappa k us | HFixed p => p end.

Definition horn_ob (h : horn) : obligation := mkOb (h_label h) (h_hyps h) (hgoal_formula (h_goal h)).

Definition normalize (ob : obligation) : list obligation :=
  let hs := flat_map conjuncts (ob_hyps ob) in
  map (fun g => mkOb (ob_label ob) hs g) (conjuncts (ob_goal ob)).

Definition hyp_shape_ok (h : formula) : bool :=
  match h with FKappa _ _ => true | _ => kfree h end.

Definition to_horn (ob : obligation) : result string horn :=
  let* _ := require (forallb hyp_shape_ok (ob_hyps ob)) "an unknown under a negation or a disjunction" in
  match ob_goal ob with
  | FKappa k us => Ok (mkHorn (ob_label ob) (ob_hyps ob) (HKappa k us))
  | g => if kfree g then Ok (mkHorn (ob_label ob) (ob_hyps ob) (HFixed g))
         else Err "an unknown under a negation or a disjunction"
  end.

Definition horn_of (obs : list obligation) : result string (list horn) :=
  mapM to_horn (flat_map normalize obs).

(** Normalization keeps the meaning: the obligation holds iff all its
    pieces do. *)
Lemma normalize_holds : forall ki ρ ob,
  ob_holds ki ρ ob <-> Forall (ob_holds ki ρ) (normalize ob).
Proof.
  intros ki ρ ob. unfold normalize.
  assert (Hh : Forall (holds ki ρ) (flat_map conjuncts (ob_hyps ob)) <-> Forall (holds ki ρ) (ob_hyps ob)).
  { induction (ob_hyps ob) as [|h hs IH]; cbn; [tauto | ].
    rewrite Forall_app, IH, <- holds_conjuncts. split; [intros [H1 H2]; constructor; auto | intros H; inversion H; auto]. }
  rewrite Forall_forall. unfold ob_holds at 1. rewrite (holds_conjuncts ki ρ (ob_goal ob)), <- Hh.
  split.
  - intros H ob' Hin. apply in_map_iff in Hin as (g & <- & Hg). unfold ob_holds. cbn. intros Hhyp.
    exact (proj1 (Forall_forall _ _) (H Hhyp) g Hg).
  - intros H Hhyp. apply Forall_forall. intros g Hg.
    exact (H _ (in_map _ _ _ Hg) Hhyp).
Qed.
