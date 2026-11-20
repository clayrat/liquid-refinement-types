(** * Sorted simultaneous substitution

    A substitution has three parts, one per namespace: integer variables
    are replaced by terms, boolean variables by boolean atoms, arrays and
    lists by arrays and lists.  The last part acts under [len]:
    [[a ↦ xs](len a) = len xs].
    The boolean part allows [[b ↦ true]], in formulas and in the
    arguments of [κ] alike.  Every part is simultaneous: the image of a
    name is never substituted again.  Formulas have no binders, so there
    is no capture.

    [subst_val σ ρ] is the valuation that gives every name the value of
    its image under [ρ]: substituting in the formula is evaluating under
    the changed valuation ([teval_subst], [pevalb_subst]).  A
    substitution that sends the names of a scope to well-scoped images
    keeps formulas well-scoped and their [κ] well-sorted
    ([formula_ok_subst]).

    [ksubst] builds the substitution of the formal parameters of a [κ]
    (or of any list of sorted names) by actual arguments. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula.

Local Open Scope Z_scope.

Record subst : Type := mkSubst {
  s_int : list (string * term);
  s_bool : list (string * batom);
  s_arr : list (string * string)
}.

Definition subst_empty : subst := mkSubst [] [] [].

Definition add_int (x : string) (t : term) (σ : subst) : subst :=
  mkSubst ((x, t) :: s_int σ) (s_bool σ) (s_arr σ).
Definition add_bool (x : string) (b : batom) (σ : subst) : subst :=
  mkSubst (s_int σ) ((x, b) :: s_bool σ) (s_arr σ).
Definition add_arr (x : string) (a : string) (σ : subst) : subst :=
  mkSubst (s_int σ) (s_bool σ) ((x, a) :: s_arr σ).

Definition arr_image (σ : subst) (a : string) : string :=
  match assoc a (s_arr σ) with Some a' => a' | None => a end.

Fixpoint tsubst (σ : subst) (t : term) : term :=
  match t with
  | TVar x => match assoc x (s_int σ) with Some t' => t' | None => TVar x end
  | TConst z => TConst z
  | TAdd t1 t2 => TAdd (tsubst σ t1) (tsubst σ t2)
  | TSub t1 t2 => TSub (tsubst σ t1) (tsubst σ t2)
  | TMul k t => TMul k (tsubst σ t)
  | TLen a => TLen (arr_image σ a)
  end.

Definition bsubst (σ : subst) (b : batom) : batom :=
  match b with
  | BVar x => match assoc x (s_bool σ) with Some b' => b' | None => BVar x end
  | BConst c => BConst c
  end.

Definition asubst (σ : subst) (u : arg) : arg :=
  match u with
  | UInt t => UInt (tsubst σ t)
  | UBool b => UBool (bsubst σ b)
  end.

Fixpoint fsubst (σ : subst) (p : formula) : formula :=
  match p with
  | FLe t1 t2 => FLe (tsubst σ t1) (tsubst σ t2)
  | FLt t1 t2 => FLt (tsubst σ t1) (tsubst σ t2)
  | FEq t1 t2 => FEq (tsubst σ t1) (tsubst σ t2)
  | FAtom b => FAtom (bsubst σ b)
  | FKappa k us => FKappa k (map (asubst σ) us)
  | FAnd p q => FAnd (fsubst σ p) (fsubst σ q)
  | FOr p q => FOr (fsubst σ p) (fsubst σ q)
  | FNot p => FNot (fsubst σ p)
  end.

(** ** Substitution and valuations *)

Definition subst_val (σ : subst) (ρ : valuation) : valuation :=
  mkVal (fun x => match assoc x (s_int σ) with Some t => teval ρ t | None => vint ρ x end)
        (fun b => match assoc b (s_bool σ) with Some b' => beval ρ b' | None => vbool ρ b end)
        (fun a => vlen ρ (arr_image σ a)).

Lemma teval_subst : forall σ ρ t, teval ρ (tsubst σ t) = teval (subst_val σ ρ) t.
Proof.
  intros σ ρ t. induction t; cbn; try reflexivity; try congruence.
  destruct (assoc x (s_int σ)); reflexivity.
Qed.

Lemma beval_subst : forall σ ρ b, beval ρ (bsubst σ b) = beval (subst_val σ ρ) b.
Proof. intros σ ρ [x | c]; cbn; [destruct (assoc x (s_bool σ)) | ]; reflexivity. Qed.

Lemma aeval_subst : forall σ ρ u, aeval ρ (asubst σ u) = aeval (subst_val σ ρ) u.
Proof. intros σ ρ [t | b]; cbn; [rewrite teval_subst | rewrite beval_subst]; reflexivity. Qed.

Lemma pevalb_subst : forall ki σ ρ p, pevalb ki ρ (fsubst σ p) = pevalb ki (subst_val σ ρ) p.
Proof.
  intros ki σ ρ p. induction p; cbn; rewrite ?teval_subst, ?beval_subst; try congruence.
  rewrite map_map. f_equal. apply map_ext. apply aeval_subst.
Qed.

Lemma holds_subst : forall ki σ ρ p, holds ki ρ (fsubst σ p) <-> holds ki (subst_val σ ρ) p.
Proof. intros ki σ ρ p. rewrite <- !pevalb_holds. now rewrite pevalb_subst. Qed.

Lemma kfree_subst : forall σ p, kfree (fsubst σ p) = kfree p.
Proof. intros σ p. induction p; cbn; congruence. Qed.

Lemma is_ftrue_subst : forall σ p, is_ftrue p = true -> fsubst σ p = p.
Proof. intros σ p H. destruct p as [ | | | [|[]] | | | | ]; try discriminate H. reflexivity. Qed.

Lemma fsubst_fand : forall ki ρ σ p q,
  holds ki ρ (fsubst σ (fand p q)) <-> holds ki ρ (fsubst σ p) /\ holds ki ρ (fsubst σ q).
Proof. intros ki ρ σ p q. rewrite !holds_subst. apply holds_fand. Qed.

(** ** Sorts and scopes are preserved *)

Definition subst_ok (sc sc' : scope) (σ : subst) : Prop :=
  (forall x, In x (sc_int sc) ->
     match assoc x (s_int σ) with
     | Some t => incl (tvars t) (sc_int sc') /\ incl (tlens t) (sc_arr sc')
     | None => In x (sc_int sc')
     end) /\
  (forall b, In b (sc_bool sc) ->
     match assoc b (s_bool σ) with
     | Some b' => incl (bvars b') (sc_bool sc')
     | None => In b (sc_bool sc')
     end) /\
  (forall a, In a (sc_arr sc) -> In (arr_image σ a) (sc_arr sc')).

Lemma tsubst_scope : forall sc sc' σ t, subst_ok sc sc' σ ->
  incl (tvars t) (sc_int sc) -> incl (tlens t) (sc_arr sc) ->
  incl (tvars (tsubst σ t)) (sc_int sc') /\ incl (tlens (tsubst σ t)) (sc_arr sc').
Proof.
  intros sc sc' σ t (Hi & _ & Ha). unfold incl.
  induction t; cbn; intros Hx Hl.
  - specialize (Hi x (Hx x (or_introl eq_refl))).
    destruct (assoc x (s_int σ)) as [t' | ]; [exact Hi | ].
    cbn. split; [intros y [<- | []]; exact Hi | intros _ []].
  - split; intros _ [].
  - destruct IHt1 as [A1 B1]; [intros; apply Hx, in_or_app; auto | intros; apply Hl, in_or_app; auto | ].
    destruct IHt2 as [A2 B2]; [intros; apply Hx, in_or_app; auto | intros; apply Hl, in_or_app; auto | ].
    split; intros y Hy; apply in_app_or in Hy as [Hy | Hy]; auto.
  - destruct IHt1 as [A1 B1]; [intros; apply Hx, in_or_app; auto | intros; apply Hl, in_or_app; auto | ].
    destruct IHt2 as [A2 B2]; [intros; apply Hx, in_or_app; auto | intros; apply Hl, in_or_app; auto | ].
    split; intros y Hy; apply in_app_or in Hy as [Hy | Hy]; auto.
  - apply IHt; auto.
  - split; [intros _ [] | ]. intros y [<- | []]. apply Ha, Hl. now left.
Qed.

Lemma sorts_match_subst : forall σ us ss, sorts_match (map (asubst σ) us) ss = sorts_match us ss.
Proof.
  intros σ us. induction us as [|u us IH]; intros [|s ss]; cbn; try reflexivity.
  rewrite IH. destruct u; reflexivity.
Qed.

Lemma kappas_ok_subst : forall K σ p, kappas_ok K (fsubst σ p) = kappas_ok K p.
Proof.
  intros K σ p. induction p; cbn; try congruence.
  destruct (assoc k K); [apply sorts_match_subst | reflexivity].
Qed.

Lemma incl_flat_map : forall {A} (f : A -> list string) (l : list A) zs,
  (forall a, In a l -> incl (f a) zs) -> incl (flat_map f l) zs.
Proof. intros A f l zs H x Hx. apply in_flat_map in Hx as (a & Ha & Hx). exact (H a Ha x Hx). Qed.

Lemma incl_flat_map_in : forall {A} (f : A -> list string) (l : list A) zs a,
  incl (flat_map f l) zs -> In a l -> incl (f a) zs.
Proof. intros A f l zs a H Ha x Hx. apply H, in_flat_map. eauto. Qed.

Lemma bsubst_scope : forall sc sc' σ b, subst_ok sc sc' σ ->
  incl (bvars b) (sc_bool sc) -> incl (bvars (bsubst σ b)) (sc_bool sc').
Proof.
  intros sc sc' σ [x | c] (_ & Hb & _) H; cbn in *; [ | apply incl_nil_l].
  specialize (Hb x (H x (or_introl eq_refl))).
  destruct (assoc x (s_bool σ)) as [b' | ]; [exact Hb | ].
  intros y [<- | []]. exact Hb.
Qed.

Lemma fsubst_scope : forall sc sc' σ p, subst_ok sc sc' σ ->
  incl (fvars p) (sc_int sc) -> incl (fbvars p) (sc_bool sc) -> incl (flens p) (sc_arr sc) ->
  incl (fvars (fsubst σ p)) (sc_int sc') /\ incl (fbvars (fsubst σ p)) (sc_bool sc')
  /\ incl (flens (fsubst σ p)) (sc_arr sc').
Proof.
  intros sc sc' σ p Hσ. induction p; cbn; intros Hx Hb Hl.
  1-3:
    apply incl_app_inv in Hx as [Hx1 Hx2], Hl as [Hl1 Hl2];
    destruct (tsubst_scope sc sc' σ t1 Hσ Hx1 Hl1) as [A1 B1]; destruct (tsubst_scope sc sc' σ t2 Hσ Hx2 Hl2) as [A2 B2];
    split; [apply incl_app; auto | split; [apply incl_nil_l | apply incl_app; auto]].
  - split; [apply incl_nil_l | split; [apply (bsubst_scope sc); auto | apply incl_nil_l]].
  - rewrite !flat_map_concat_map, !map_map, <- !flat_map_concat_map.
    split; [ | split]; apply incl_flat_map; intros [t | b] Hu; cbn; try apply incl_nil_l.
    + exact (proj1 (tsubst_scope sc sc' σ t Hσ (incl_flat_map_in uvars us _ _ Hx Hu)
                                              (incl_flat_map_in ulens us _ _ Hl Hu))).
    + exact (bsubst_scope sc sc' σ b Hσ (incl_flat_map_in ubvars us _ _ Hb Hu)).
    + exact (proj2 (tsubst_scope sc sc' σ t Hσ (incl_flat_map_in uvars us _ _ Hx Hu)
                                              (incl_flat_map_in ulens us _ _ Hl Hu))).
  - apply incl_app_inv in Hx as [Hx1 Hx2], Hb as [Hb1 Hb2], Hl as [Hl1 Hl2].
    destruct (IHp1 Hx1 Hb1 Hl1) as (A1 & B1 & C1). destruct (IHp2 Hx2 Hb2 Hl2) as (A2 & B2 & C2).
    split; [ | split]; apply incl_app; auto.
  - apply incl_app_inv in Hx as [Hx1 Hx2], Hb as [Hb1 Hb2], Hl as [Hl1 Hl2].
    destruct (IHp1 Hx1 Hb1 Hl1) as (A1 & B1 & C1). destruct (IHp2 Hx2 Hb2 Hl2) as (A2 & B2 & C2).
    split; [ | split]; apply incl_app; auto.
  - apply IHp; auto.
Qed.

Lemma formula_ok_subst : forall K sc sc' σ p,
  subst_ok sc sc' σ -> formula_ok K sc p = true -> formula_ok K sc' (fsubst σ p) = true.
Proof.
  intros K sc sc' σ p Hσ H. unfold formula_ok in *.
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hx Hb].
  rewrite kappas_ok_subst, Hk, andb_true_r.
  rewrite subset_In in Hx, Hb, Hl.
  destruct (fsubst_scope sc sc' σ p Hσ Hx Hb Hl) as (A & B & C).
  rewrite (proj2 (subset_In _ _) A), (proj2 (subset_In _ _) B), (proj2 (subset_In _ _) C). reflexivity.
Qed.

(** ** Substituting sorted formals by arguments *)

Fixpoint ksubst (formals : list (string * sort)) (us : list arg) : subst :=
  match formals, us with
  | (x, _) :: fs, UInt t :: us' => add_int x t (ksubst fs us')
  | (x, _) :: fs, UBool b :: us' => add_bool x b (ksubst fs us')
  | _, _ => subst_empty
  end.
