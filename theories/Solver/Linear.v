(** * Linear forms and atoms of the difference fragment

    The linear form of a term is a list of coefficients at nodes and a
    constant; [add_coef] collects like terms, so that after [lin]
    [n − (i + 1) < n − i] is a constant atom.  [lin_sound]: the form has
    the value of the term under the node valuation [nval ρ] of a logical
    valuation [ρ], in which a boolean variable is [0] or [1].

    An atom [t₁ ≤ t₂] is classified by the form of [t₂ − t₁ ≥ 0]: no
    node gives [true] or [false], one node with coefficient [±1] or two
    with [1] and [−1] give an edge of the graph, anything else is
    outside the fragment.

    [decomp pos p] splits [p] (if [pos]) or [¬p] (otherwise) into a
    conjunction of constraints: [∧] on the positive side and [∨] on the
    negative side split, negation flips the side, [=] is two
    inequalities, [¬(t₁ ≤ t₂)] is [t₂ + 1 ≤ t₁] over ℤ, and a boolean
    variable [b] is the edge [1 ≤ b] or [b ≤ 0].  A piece outside the
    fragment is kept as [COut] with its own meaning.  [decomp_iff]: the
    conjunction of the pieces is equivalent to [p] or [¬p]. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Solver Require Import Diff.

Local Open Scope Z_scope.

Definition linform : Type := (list (node * Z) * Z)%type.

Fixpoint lsum (v : nvaluation) (cs : list (node * Z)) : Z :=
  match cs with
  | [] => 0
  | (n, c) :: cs' => c * aval v n + lsum v cs'
  end.

Definition leval (v : nvaluation) (l : linform) : Z := lsum v (fst l) + snd l.

Fixpoint add_coef (n : node) (c : Z) (cs : list (node * Z)) : list (node * Z) :=
  match cs with
  | [] => if c =? 0 then [] else [(n, c)]
  | (m, d) :: cs' =>
      if node_eqb n m
      then (if c + d =? 0 then cs' else (m, c + d) :: cs')
      else (m, d) :: add_coef n c cs'
  end.

Lemma add_coef_sum : forall v n c cs, lsum v (add_coef n c cs) = c * aval v n + lsum v cs.
Proof.
  intros v n c cs. induction cs as [|[m d] cs IH]; cbn.
  - destruct (Z.eqb_spec c 0); cbn; [subst; lia | lia].
  - destruct (node_eqb n m) eqn:E.
    + apply node_eqb_eq in E. subst m.
      destruct (Z.eqb_spec (c + d) 0) as [H | H]; cbn.
      * assert (d = - c) by lia. subst d. lia.
      * rewrite Z.mul_add_distr_r. lia.
    + cbn. rewrite IH. lia.
Qed.

Definition ladd (l1 l2 : linform) : linform :=
  (fold_left (fun acc p => add_coef (fst p) (snd p) acc) (fst l2) (fst l1), snd l1 + snd l2).

Lemma fold_add_coef_sum : forall v cs acc,
  lsum v (fold_left (fun acc p => add_coef (fst p) (snd p) acc) cs acc) = lsum v cs + lsum v acc.
Proof.
  intros v cs. induction cs as [|[n c] cs IH]; intros acc; cbn; [reflexivity | ].
  rewrite IH, add_coef_sum. lia.
Qed.

Lemma ladd_eval : forall v l1 l2, leval v (ladd l1 l2) = leval v l1 + leval v l2.
Proof. intros v [cs1 c1] [cs2 c2]. unfold leval, ladd. cbn. rewrite fold_add_coef_sum. lia. Qed.

Definition lscale (k : Z) (l : linform) : linform :=
  if k =? 0 then ([], 0) else (map (fun p => (fst p, k * snd p)) (fst l), k * snd l).

Lemma lsum_scale : forall v k cs, lsum v (map (fun p => (fst p, k * snd p)) cs) = k * lsum v cs.
Proof. intros v k cs. induction cs as [|[n d] cs IH]; cbn; [ring | rewrite IH; ring]. Qed.

Lemma lscale_eval : forall v k l, leval v (lscale k l) = k * leval v l.
Proof.
  intros v k [cs c]. unfold lscale, leval. destruct (Z.eqb_spec k 0) as [-> | H]; cbn; [lia | ].
  rewrite lsum_scale. ring.
Qed.

Fixpoint lin (t : term) : linform :=
  match t with
  | TVar x => ([(NInt x, 1)], 0)
  | TConst z => ([], z)
  | TAdd t1 t2 => ladd (lin t1) (lin t2)
  | TSub t1 t2 => ladd (lin t1) (lscale (-1) (lin t2))
  | TMul k t => lscale k (lin t)
  | TLen a => ([(NLen a, 1)], 0)
  end.

(** The node valuation of a logical valuation. *)
Definition nval (ρ : valuation) : nvaluation :=
  fun n => match n with
           | NZero => 0
           | NInt x => vint ρ x
           | NBool b => if vbool ρ b then 1 else 0
           | NLen a => vlen ρ a
           end.

Lemma lin_sound : forall ρ t, leval (nval ρ) (lin t) = teval ρ t.
Proof.
  intros ρ t. induction t; cbn [lin teval].
  - unfold leval. cbn [lsum fst snd aval nval]. lia.
  - unfold leval. cbn [lsum fst snd aval nval]. lia.
  - rewrite ladd_eval. lia.
  - rewrite ladd_eval, lscale_eval. lia.
  - rewrite lscale_eval. lia.
  - unfold leval. cbn [lsum fst snd aval nval]. lia.
Qed.

(** ** Constraints *)

Inductive catom : Type :=
| CTrue
| CFalse
| CEdge (e : edge)
| COut (p : formula) (pos : bool).

Definition meaning (ki : kinterp) (ρ : valuation) (pos : bool) (p : formula) : Prop :=
  if pos then holds ki ρ p else ~ holds ki ρ p.

Definition csem (ki : kinterp) (ρ : valuation) (a : catom) : Prop :=
  match a with
  | CTrue => True
  | CFalse => False
  | CEdge e => edge_sat (nval ρ) e
  | COut p pos => meaning ki ρ pos p
  end.

(** [0 ≤ l] as a constraint, if it is in the fragment. *)
Definition classify (l : linform) : option catom :=
  let (cs, c) := l in
  match cs with
  | [] => Some (if 0 <=? c then CTrue else CFalse)
  | [(x, 1)] => Some (CEdge (NZero, - c, x))
  | [(x, -1)] => Some (CEdge (x, - c, NZero))
  | [(x, 1); (y, -1)] => Some (CEdge (y, - c, x))
  | [(y, -1); (x, 1)] => Some (CEdge (y, - c, x))
  | _ => None
  end.

Lemma classify_sound : forall ki ρ l a, classify l = Some a -> (csem ki ρ a <-> 0 <= leval (nval ρ) l).
Proof.
  intros ki ρ [cs c] a H. unfold classify in H. unfold leval. cbn [fst snd].
  destruct cs as [|[x d] [|[y d'] [|]]]; try discriminate H.
  - injection H as <-. cbn. destruct (Z.leb_spec 0 c); cbn; split; intros; lia.
  - destruct d as [|[d|d|]|[d|d|]]; try discriminate H; injection H as <-;
      unfold csem, edge_sat; cbn [e_src e_w e_dst lsum]; change (aval (nval ρ) NZero) with 0; lia.
  - destruct d as [|[d|d|]|[d|d|]]; try discriminate H;
      destruct d' as [|[d'|d'|]|[d'|d'|]]; try discriminate H; injection H as <-;
      unfold csem, edge_sat; cbn [e_src e_w e_dst lsum]; change (aval (nval ρ) NZero) with 0; lia.
  - destruct d as [|[d|d|]|[d|d|]], d' as [|[d'|d'|]|[d'|d'|]]; discriminate H.
Qed.

(** [t₁ ≤ t₂] standing for the piece [p] of side [pos]. *)
Definition le_atom (t1 t2 : term) (p : formula) (pos : bool) : catom :=
  match classify (lin (TSub t2 t1)) with
  | Some a => a
  | None => COut p pos
  end.

Lemma le_atom_spec : forall ki ρ t1 t2 p pos,
  le_atom t1 t2 p pos = COut p pos \/ (csem ki ρ (le_atom t1 t2 p pos) <-> teval ρ t1 <= teval ρ t2).
Proof.
  intros ki ρ t1 t2 p pos. unfold le_atom.
  destruct (classify (lin (TSub t2 t1))) as [a | ] eqn:E; [right | left; reflexivity].
  rewrite (classify_sound ki ρ _ a E), lin_sound. cbn. lia.
Qed.

Fixpoint decomp (pos : bool) (p : formula) : list catom :=
  match p with
  | FLe t1 t2 => if pos then [le_atom t1 t2 p pos] else [le_atom (TAdd t2 (TConst 1)) t1 p pos]
  | FLt t1 t2 => if pos then [le_atom (TAdd t1 (TConst 1)) t2 p pos] else [le_atom t2 t1 p pos]
  | FEq t1 t2 => if pos then [le_atom t1 t2 p pos; le_atom t2 t1 p pos] else [COut p pos]
  | FAtom (BConst c) => if Bool.eqb c pos then [] else [CFalse]
  | FAtom (BVar b) => if pos then [CEdge (NZero, 1, NBool b)] else [CEdge (NBool b, 0, NZero)]
  | FAnd q r => if pos then decomp pos q ++ decomp pos r else [COut p pos]
  | FOr q r => if pos then [COut p pos] else decomp pos q ++ decomp pos r
  | FNot q => decomp (negb pos) q
  | FKappa _ _ => [COut p pos]
  end.

Lemma Forall_one : forall {A} (P : A -> Prop) a, Forall P [a] <-> P a.
Proof. intros A P a. split; [intros H; inversion H; auto | intros H; constructor; auto]. Qed.

Lemma Forall_two : forall {A} (P : A -> Prop) a b, Forall P [a; b] <-> P a /\ P b.
Proof.
  intros A P a b. split; [intros H; inversion H as [|? ? Ha Hb]; inversion Hb; auto | ].
  intros [Ha Hb]. repeat constructor; auto.
Qed.

Theorem decomp_iff : forall ki ρ pos p, Forall (csem ki ρ) (decomp pos p) <-> meaning ki ρ pos p.
Proof.
  intros ki ρ pos p. revert pos. induction p; intros pos; unfold meaning; cbn [decomp holds].
  - destruct pos; rewrite Forall_one;
      [destruct (le_atom_spec ki ρ t1 t2 (FLe t1 t2) true) as [-> | ->]
      | destruct (le_atom_spec ki ρ (TAdd t2 (TConst 1)) t1 (FLe t1 t2) false) as [-> | ->]];
      cbn; try reflexivity; lia.
  - destruct pos; rewrite Forall_one;
      [destruct (le_atom_spec ki ρ (TAdd t1 (TConst 1)) t2 (FLt t1 t2) true) as [-> | ->]
      | destruct (le_atom_spec ki ρ t2 t1 (FLt t1 t2) false) as [-> | ->]];
      cbn; try reflexivity; lia.
  - destruct pos; [ | rewrite Forall_one; reflexivity].
    rewrite Forall_two.
    destruct (le_atom_spec ki ρ t1 t2 (FEq t1 t2) true) as [E1 | E1];
      destruct (le_atom_spec ki ρ t2 t1 (FEq t1 t2) true) as [E2 | E2];
      try rewrite E1; try rewrite E2; cbn; try rewrite E1; try rewrite E2; lia.
  - destruct b as [x | c]; cbn.
    + destruct pos; rewrite Forall_one; unfold csem, edge_sat; cbn; destruct (vbool ρ x); cbn;
        split; intros; try lia; try congruence.
    + destruct c, pos; cbn; (split; [intros H; try (inversion H; contradiction); try constructor | ]);
        try (intros; constructor); try congruence; try (intros H; exfalso; apply H; reflexivity).
  - rewrite Forall_one. reflexivity.
  - destruct pos; [ | rewrite Forall_one; reflexivity].
    rewrite Forall_app, (IHp1 true), (IHp2 true). reflexivity.
  - destruct pos; [rewrite Forall_one; reflexivity | ].
    rewrite Forall_app, (IHp1 false), (IHp2 false). cbn. tauto.
  - rewrite (IHp (negb pos)). destruct pos; cbn; [reflexivity | ].
    destruct (holds_dec ki ρ p); tauto.
Qed.

(** A constraint outside the fragment: the pieces that are not. *)
Definition is_out (a : catom) : bool := match a with COut _ _ => true | _ => false end.
