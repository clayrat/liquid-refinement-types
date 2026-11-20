(** * Formulas of the logic

    The logic of obligations, independent of the programs (Lang/):

      t ::= x | n | t + t | t − t | k·t | len a
      β ::= b | true | false
      u ::= t | β
      p ::= t ≤ t | t < t | t = t | β | κ(u₁, …, uₖ) | p ∧ p | p ∨ p | ¬p

    [x] is an integer variable, [b] a boolean one, [a] the name of an
    array or a list, which occurs only under [len]; [u] is an argument with its
    sort explicit, Int or Bool.  The three kinds of names live in three
    namespaces: a valuation gives an integer to every [x], a boolean to
    every [b] and an integer to every [len a].  It is total, so that the
    duality [¬(t₁ ≤ t₂) ≡ t₂ < t₁] holds, on which the solver stands.

    An unknown predicate [κ] is in the syntax from the start; a formula
    without one is the input of the first algorithm, and an assignment of
    formulas to the [κ] is applied by substitution (Liquid/Weaken.v).
    The semantics interprets [κ] by a parameter [ki].

    Two semantics: [holds], valued in [Prop], for the statements, and
    [pevalb], valued in [bool], on a concrete valuation, for checking
    counter-models; [pevalb_holds] says they agree.

    The sorted scopes of the last section check that a formula mentions
    only the names given to it with their sorts, and that every [κ] is
    applied to arguments of the sorts of its signature. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.

Local Open Scope Z_scope.

Inductive sort : Type := SInt | SBool.

Inductive term : Type :=
| TVar (x : string)
| TConst (z : Z)
| TAdd (t1 t2 : term)
| TSub (t1 t2 : term)
| TMul (k : Z) (t : term)
| TLen (a : string).

Inductive batom : Type :=
| BVar (b : string)
| BConst (c : bool).

Inductive arg : Type :=
| UInt (t : term)
| UBool (b : batom).

Inductive formula : Type :=
| FLe (t1 t2 : term)
| FLt (t1 t2 : term)
| FEq (t1 t2 : term)
| FAtom (b : batom)
| FKappa (k : string) (us : list arg)
| FAnd (p q : formula)
| FOr (p q : formula)
| FNot (p : formula).

(** ** Decidable equality *)

Definition sort_eq_dec (s1 s2 : sort) : {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Definition term_eq_dec (t1 t2 : term) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality; first [apply string_dec | apply Z.eq_dec]. Defined.

Definition batom_eq_dec (b1 b2 : batom) : {b1 = b2} + {b1 <> b2}.
Proof. decide equality; first [apply string_dec | apply bool_dec]. Defined.

Definition arg_eq_dec (u1 u2 : arg) : {u1 = u2} + {u1 <> u2}.
Proof. decide equality; first [apply term_eq_dec | apply batom_eq_dec]. Defined.

Definition formula_eq_dec (p q : formula) : {p = q} + {p <> q}.
Proof.
  decide equality;
    first [apply term_eq_dec | apply batom_eq_dec | apply string_dec | apply (list_eq_dec arg_eq_dec)].
Defined.

Definition formula_eqb (p q : formula) : bool := if formula_eq_dec p q then true else false.

(** ** Smart constructors

    [true] and [false] are boolean atoms.  [fand] drops a conjunct
    [true], so that an obligation [φ ⊢ true] is not built from the
    precondition [true] of addition; [fconj] is the conjunction of a
    list, [true] for the empty one. *)

Definition ftrue : formula := FAtom (BConst true).
Definition ffalse : formula := FAtom (BConst false).

Definition is_ftrue (p : formula) : bool :=
  match p with FAtom (BConst true) => true | _ => false end.

Definition fand (p q : formula) : formula :=
  if is_ftrue p then q else if is_ftrue q then p else FAnd p q.

Definition fconj (ps : list formula) : formula := fold_right fand ftrue ps.

Definition fimp (p q : formula) : formula := FOr (FNot p) q.

(** The conjuncts of a formula, with [true] dropped. *)
Fixpoint conjuncts (p : formula) : list formula :=
  match p with
  | FAnd p q => conjuncts p ++ conjuncts q
  | _ => if is_ftrue p then [] else [p]
  end.

(** ** Unknown predicates *)

Fixpoint kfree (p : formula) : bool :=
  match p with
  | FKappa _ _ => false
  | FAnd p q | FOr p q => kfree p && kfree q
  | FNot p => kfree p
  | _ => true
  end.

(** ** Semantics *)

Record valuation : Type := mkVal {
  vint : string -> Z;
  vbool : string -> bool;
  vlen : string -> Z
}.

Inductive lit : Type :=
| LInt (z : Z)
| LBool (c : bool).

Definition lit_eq_dec (l1 l2 : lit) : {l1 = l2} + {l1 <> l2}.
Proof. decide equality; first [apply Z.eq_dec | apply bool_dec]. Defined.

(** An interpretation of the unknown predicates; [no_kappa] reads every
    [κ] as false. *)
Definition kinterp : Type := string -> list lit -> bool.

Definition no_kappa : kinterp := fun _ _ => false.

Fixpoint teval (ρ : valuation) (t : term) : Z :=
  match t with
  | TVar x => vint ρ x
  | TConst z => z
  | TAdd t1 t2 => teval ρ t1 + teval ρ t2
  | TSub t1 t2 => teval ρ t1 - teval ρ t2
  | TMul k t => k * teval ρ t
  | TLen a => vlen ρ a
  end.

Definition beval (ρ : valuation) (b : batom) : bool :=
  match b with
  | BVar x => vbool ρ x
  | BConst c => c
  end.

Definition aeval (ρ : valuation) (u : arg) : lit :=
  match u with
  | UInt t => LInt (teval ρ t)
  | UBool b => LBool (beval ρ b)
  end.

Fixpoint holds (ki : kinterp) (ρ : valuation) (p : formula) : Prop :=
  match p with
  | FLe t1 t2 => teval ρ t1 <= teval ρ t2
  | FLt t1 t2 => teval ρ t1 < teval ρ t2
  | FEq t1 t2 => teval ρ t1 = teval ρ t2
  | FAtom b => beval ρ b = true
  | FKappa k us => ki k (map (aeval ρ) us) = true
  | FAnd p q => holds ki ρ p /\ holds ki ρ q
  | FOr p q => holds ki ρ p \/ holds ki ρ q
  | FNot p => ~ holds ki ρ p
  end.

Fixpoint pevalb (ki : kinterp) (ρ : valuation) (p : formula) : bool :=
  match p with
  | FLe t1 t2 => teval ρ t1 <=? teval ρ t2
  | FLt t1 t2 => teval ρ t1 <? teval ρ t2
  | FEq t1 t2 => teval ρ t1 =? teval ρ t2
  | FAtom b => beval ρ b
  | FKappa k us => ki k (map (aeval ρ) us)
  | FAnd p q => pevalb ki ρ p && pevalb ki ρ q
  | FOr p q => pevalb ki ρ p || pevalb ki ρ q
  | FNot p => negb (pevalb ki ρ p)
  end.

Lemma pevalb_holds : forall ki ρ p, pevalb ki ρ p = true <-> holds ki ρ p.
Proof.
  intros ki ρ p. induction p; cbn.
  - apply Z.leb_le.
  - apply Z.ltb_lt.
  - apply Z.eqb_eq.
  - reflexivity.
  - reflexivity.
  - rewrite andb_true_iff. tauto.
  - rewrite orb_true_iff. tauto.
  - rewrite negb_true_iff. split.
    + intros H Hp. apply IHp in Hp. congruence.
    + intros H. destruct (pevalb ki ρ p); [ | reflexivity]. exfalso. apply H, IHp. reflexivity.
Qed.

Lemma holds_dec : forall ki ρ p, holds ki ρ p \/ ~ holds ki ρ p.
Proof.
  intros ki ρ p. destruct (pevalb ki ρ p) eqn:E.
  - left. apply pevalb_holds, E.
  - right. intros H. apply pevalb_holds in H. congruence.
Qed.

Lemma holds_fand : forall ki ρ p q, holds ki ρ (fand p q) <-> holds ki ρ p /\ holds ki ρ q.
Proof.
  intros ki ρ p q. unfold fand.
  destruct (is_ftrue p) eqn:Ep.
  - destruct p as [ | | | [|[]] | | | | ]; try discriminate Ep. cbn. tauto.
  - destruct (is_ftrue q) eqn:Eq.
    + destruct q as [ | | | [|[]] | | | | ]; try discriminate Eq. cbn. tauto.
    + reflexivity.
Qed.

Lemma holds_fconj : forall ki ρ ps, holds ki ρ (fconj ps) <-> Forall (holds ki ρ) ps.
Proof.
  intros ki ρ ps. induction ps as [|p ps IH]; cbn.
  - split; constructor.
  - rewrite holds_fand, IH. split; [intros [H1 H2]; constructor; auto | intros H; inversion H; auto].
Qed.

Lemma is_ftrue_holds : forall ki ρ p, is_ftrue p = true -> holds ki ρ p.
Proof. intros ki ρ p H. destruct p as [ | | | [|[]] | | | | ]; try discriminate H. reflexivity. Qed.

Lemma holds_conjuncts : forall ki ρ p, holds ki ρ p <-> Forall (holds ki ρ) (conjuncts p).
Proof.
  intros ki ρ p.
  assert (Hleaf : forall q, holds ki ρ q <-> Forall (holds ki ρ) (if is_ftrue q then [] else [q])).
  { intros q. destruct (is_ftrue q) eqn:E.
    - split; [constructor | intros _; apply is_ftrue_holds; exact E].
    - split; [intros H; constructor; [exact H | constructor] | intros H; inversion H; assumption]. }
  induction p; try apply Hleaf.
  cbn. rewrite Forall_app, <- IHp1, <- IHp2. tauto.
Qed.

(** A [κ]-free formula does not depend on the interpretation of [κ]. *)
Lemma pevalb_kfree : forall ki ki' ρ p, kfree p = true -> pevalb ki ρ p = pevalb ki' ρ p.
Proof.
  intros ki ki' ρ p. induction p; cbn; intros H; try reflexivity; try discriminate H.
  - apply andb_prop in H as [H1 H2]. now rewrite IHp1, IHp2.
  - apply andb_prop in H as [H1 H2]. now rewrite IHp1, IHp2.
  - now rewrite IHp.
Qed.

Lemma holds_kfree : forall ki ki' ρ p, kfree p = true -> holds ki ρ p <-> holds ki' ρ p.
Proof. intros ki ki' ρ p H. rewrite <- !pevalb_holds. now rewrite (pevalb_kfree ki ki' ρ p H). Qed.

(** ** Free names

    The names of each namespace that a formula mentions: integer
    variables, boolean variables, arrays and lists under [len]. *)

Fixpoint tvars (t : term) : list string :=
  match t with
  | TVar x => [x]
  | TConst _ | TLen _ => []
  | TAdd t1 t2 | TSub t1 t2 => tvars t1 ++ tvars t2
  | TMul _ t => tvars t
  end.

Fixpoint tlens (t : term) : list string :=
  match t with
  | TLen a => [a]
  | TVar _ | TConst _ => []
  | TAdd t1 t2 | TSub t1 t2 => tlens t1 ++ tlens t2
  | TMul _ t => tlens t
  end.

Definition bvars (b : batom) : list string :=
  match b with BVar x => [x] | BConst _ => [] end.

Definition uvars (u : arg) : list string := match u with UInt t => tvars t | UBool _ => [] end.
Definition ubvars (u : arg) : list string := match u with UInt _ => [] | UBool b => bvars b end.
Definition ulens (u : arg) : list string := match u with UInt t => tlens t | UBool _ => [] end.

Fixpoint fvars (p : formula) : list string :=
  match p with
  | FLe t1 t2 | FLt t1 t2 | FEq t1 t2 => tvars t1 ++ tvars t2
  | FAtom _ => []
  | FKappa _ us => flat_map uvars us
  | FAnd p q | FOr p q => fvars p ++ fvars q
  | FNot p => fvars p
  end.

Fixpoint fbvars (p : formula) : list string :=
  match p with
  | FLe _ _ | FLt _ _ | FEq _ _ => []
  | FAtom b => bvars b
  | FKappa _ us => flat_map ubvars us
  | FAnd p q | FOr p q => fbvars p ++ fbvars q
  | FNot p => fbvars p
  end.

Fixpoint flens (p : formula) : list string :=
  match p with
  | FLe t1 t2 | FLt t1 t2 | FEq t1 t2 => tlens t1 ++ tlens t2
  | FAtom _ => []
  | FKappa _ us => flat_map ulens us
  | FAnd p q | FOr p q => flens p ++ flens q
  | FNot p => flens p
  end.

(** Two valuations that agree on the names a formula mentions give it
    the same value. *)
Definition agree_on (xs bs ls : list string) (ρ1 ρ2 : valuation) : Prop :=
  (forall x, In x xs -> vint ρ1 x = vint ρ2 x) /\
  (forall b, In b bs -> vbool ρ1 b = vbool ρ2 b) /\
  (forall a, In a ls -> vlen ρ1 a = vlen ρ2 a).

Lemma teval_agree : forall ρ1 ρ2 t,
  (forall x, In x (tvars t) -> vint ρ1 x = vint ρ2 x) ->
  (forall a, In a (tlens t) -> vlen ρ1 a = vlen ρ2 a) ->
  teval ρ1 t = teval ρ2 t.
Proof.
  intros ρ1 ρ2 t. induction t; cbn; intros Hx Ha; try reflexivity.
  - apply Hx. now left.
  - rewrite IHt1, IHt2; [reflexivity | ..]; intros; first [apply Hx | apply Ha]; apply in_or_app; auto.
  - rewrite IHt1, IHt2; [reflexivity | ..]; intros; first [apply Hx | apply Ha]; apply in_or_app; auto.
  - now rewrite IHt.
  - apply Ha. now left.
Qed.

Lemma pevalb_agree : forall ki ρ1 ρ2 p,
  agree_on (fvars p) (fbvars p) (flens p) ρ1 ρ2 -> pevalb ki ρ1 p = pevalb ki ρ2 p.
Proof.
  intros ki ρ1 ρ2 p. unfold agree_on.
  assert (Happ : forall (xs ys : list string) (P : string -> Prop),
             (forall x, In x (xs ++ ys) -> P x) -> (forall x, In x xs -> P x) /\ (forall x, In x ys -> P x)).
  { intros xs ys P H. split; intros x Hx; apply H, in_or_app; auto. }
  induction p; cbn; intros (Hx & Hb & Ha).
  - apply Happ in Hx as [Hx1 Hx2]. apply Happ in Ha as [Ha1 Ha2].
    now rewrite (teval_agree ρ1 ρ2 t1), (teval_agree ρ1 ρ2 t2).
  - apply Happ in Hx as [Hx1 Hx2]. apply Happ in Ha as [Ha1 Ha2].
    now rewrite (teval_agree ρ1 ρ2 t1), (teval_agree ρ1 ρ2 t2).
  - apply Happ in Hx as [Hx1 Hx2]. apply Happ in Ha as [Ha1 Ha2].
    now rewrite (teval_agree ρ1 ρ2 t1), (teval_agree ρ1 ρ2 t2).
  - destruct b; cbn in *; [apply Hb; now left | reflexivity].
  - f_equal. apply map_ext_in. intros u Hu.
    destruct u as [t | [y | c]]; cbn; [ | | reflexivity].
    + f_equal. apply teval_agree; intros z Hz; [apply Hx | apply Ha]; apply in_flat_map; eauto.
    + f_equal. apply Hb, in_flat_map. exists (UBool (BVar y)). cbn. auto.
  - apply Happ in Hx as [Hx1 Hx2]. apply Happ in Hb as [Hb1 Hb2]. apply Happ in Ha as [Ha1 Ha2].
    now rewrite IHp1, IHp2.
  - apply Happ in Hx as [Hx1 Hx2]. apply Happ in Hb as [Hb1 Hb2]. apply Happ in Ha as [Ha1 Ha2].
    now rewrite IHp1, IHp2.
  - now rewrite IHp.
Qed.

Lemma holds_agree : forall ki ρ1 ρ2 p,
  agree_on (fvars p) (fbvars p) (flens p) ρ1 ρ2 -> holds ki ρ1 p <-> holds ki ρ2 p.
Proof. intros ki ρ1 ρ2 p H. rewrite <- !pevalb_holds. now rewrite (pevalb_agree ki ρ1 ρ2 p H). Qed.

(** ** Sorted scopes

    A scope lists the names a formula may mention, by namespace; a
    signature of unknowns gives the sorts of the formal parameters of
    every [κ].  [formula_ok] checks a formula against both: every
    integer variable, boolean variable and array is in the scope, every
    [κ] is declared and applied to arguments of its sorts. *)

Record scope : Type := mkScope {
  sc_int : list string;
  sc_bool : list string;
  sc_arr : list string
}.

Definition ksig : Type := list (string * list sort).

Definition memb (x : string) (xs : list string) : bool := existsb (String.eqb x) xs.

Lemma memb_In : forall x xs, memb x xs = true <-> In x xs.
Proof.
  intros x xs. unfold memb. rewrite existsb_exists. split.
  - intros (y & Hy & E). apply String.eqb_eq in E. now subst.
  - intros H. exists x. split; [exact H | apply String.eqb_refl].
Qed.

Fixpoint assoc {A} (x : string) (l : list (string * A)) : option A :=
  match l with
  | [] => None
  | (y, a) :: l' => if String.eqb x y then Some a else assoc x l'
  end.

Definition subset (xs ys : list string) : bool := forallb (fun x => memb x ys) xs.

Lemma subset_In : forall xs ys, subset xs ys = true <-> (forall x, In x xs -> In x ys).
Proof.
  intros xs ys. unfold subset. rewrite forallb_forall.
  split; intros H x Hx; apply memb_In; apply H, Hx.
Qed.

Definition arg_sort (u : arg) : sort := match u with UInt _ => SInt | UBool _ => SBool end.

Fixpoint sorts_match (us : list arg) (ss : list sort) : bool :=
  match us, ss with
  | [], [] => true
  | u :: us', s :: ss' => (if sort_eq_dec (arg_sort u) s then true else false) && sorts_match us' ss'
  | _, _ => false
  end.

Fixpoint kappas_ok (K : ksig) (p : formula) : bool :=
  match p with
  | FKappa k us => match assoc k K with Some ss => sorts_match us ss | None => false end
  | FAnd p q | FOr p q => kappas_ok K p && kappas_ok K q
  | FNot p => kappas_ok K p
  | _ => true
  end.

Definition formula_ok (K : ksig) (sc : scope) (p : formula) : bool :=
  subset (fvars p) (sc_int sc) && subset (fbvars p) (sc_bool sc) && subset (flens p) (sc_arr sc)
  && kappas_ok K p.

(** With no unknowns declared, a well-formed formula has none. *)
Lemma formula_ok_kfree : forall sc p, formula_ok [] sc p = true -> kfree p = true.
Proof.
  intros sc p H. unfold formula_ok in H. apply andb_prop in H as [_ H].
  induction p as [| | | | k us | p IHp q IHq | p IHp q IHq | p IHp]; cbn in H |- *; try reflexivity.
  - discriminate H.
  - apply andb_prop in H as [H1 H2]. now rewrite IHp, IHq.
  - apply andb_prop in H as [H1 H2]. now rewrite IHp, IHq.
  - now apply IHp.
Qed.

(** ** Counter-models

    A finite assignment of the names a solver found; the names it does
    not mention are [0] and [false]. *)

Record cmodel : Type := mkCModel {
  cm_int : list (string * Z);
  cm_bool : list (string * bool);
  cm_len : list (string * Z)
}.

Definition val_of_cmodel (m : cmodel) : valuation :=
  mkVal (fun x => match assoc x (cm_int m) with Some z => z | None => 0 end)
        (fun b => match assoc b (cm_bool m) with Some c => c | None => false end)
        (fun a => match assoc a (cm_len m) with Some z => z | None => 0 end).
