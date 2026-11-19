(** * The graph of difference constraints

    An edge [(a, w, b)] with [w ∈ ℤ] is the constraint

      a + w ≤ b

    over the nodes [0], [x] (an integer variable), [b] (a boolean
    variable, read as [0] or [1]) and [len a].  A valuation of the nodes
    in ℤ is a model of a graph if it satisfies every edge; the node [0]
    has the value [0].

    A graph has a model iff it has no cycle of positive weight.  [solve]
    runs Bellman–Ford for the longest paths from a virtual source at
    distance [0] from every node (the default distance of [dget]):
    - if no edge is violated after [|V|] rounds, the distances relative to
      [0] are a model;
    - otherwise the predecessors of the violated edge lead to a cycle.
    Either answer is a certificate checked before it is returned: the
    model against every edge ([check_model]), the cycle as a closed chain
    of edges of the graph with a positive sum ([cycle_ok]).  Both checks
    are proved sound, so [GModel] and [GCycle] are proved answers
    whatever the algorithm did; [GUnknown], a certificate that does not
    check, is the third answer.

    Entailment reduces to it: [a + w ≤ b] holds in every model of [G]
    iff [G] with the negation [b + (1 - w) ≤ a] has no model.  A cycle is
    then a proof of the entailment, a model is a counter-model.

    Ported from erasure-cic, Universes/Graph.v (see PORTING.md).  There
    the valuations are in ℕ and the edges [0 ≤ a] are added to every
    node; over ℤ that would make [0 ≤ i] provable without hypotheses.
    Here the valuations are in ℤ and there are no implicit edges: the
    caller adds [0 ≤ len a] and [0 ≤ b ≤ 1] (Solver/Prove.v). *)

From Stdlib Require Import String List Bool Arith ZArith Lia.
Import ListNotations.

Local Open Scope Z_scope.

Inductive node : Type :=
| NZero
| NInt (x : string)
| NBool (b : string)
| NLen (a : string).

Definition node_eq_dec (a b : node) : {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Definition node_eqb (a b : node) : bool := if node_eq_dec a b then true else false.

Lemma node_eqb_eq : forall a b, node_eqb a b = true <-> a = b.
Proof. intros a b. unfold node_eqb. destruct (node_eq_dec a b); split; congruence. Qed.

Definition nvaluation : Type := node -> Z.

Definition aval (v : nvaluation) (a : node) : Z := match a with NZero => 0 | _ => v a end.

Definition edge : Type := (node * Z * node)%type.

Definition e_src (e : edge) : node := let '(a, _, _) := e in a.
Definition e_w (e : edge) : Z := let '(_, w, _) := e in w.
Definition e_dst (e : edge) : node := let '(_, _, b) := e in b.

Definition edge_eq_dec (e f : edge) : {e = f} + {e <> f}.
Proof.
  destruct e as [[a w] b], f as [[a' w'] b'].
  destruct (node_eq_dec a a'), (Z.eq_dec w w'), (node_eq_dec b b'); subst;
  first [left; reflexivity | right; congruence].
Defined.

Definition edge_sat (v : nvaluation) (e : edge) : Prop :=
  aval v (e_src e) + e_w e <= aval v (e_dst e).

Definition edge_satb (v : nvaluation) (e : edge) : bool :=
  aval v (e_src e) + e_w e <=? aval v (e_dst e).

Lemma edge_satb_sat : forall v e, edge_satb v e = true <-> edge_sat v e.
Proof. intros v e. unfold edge_satb, edge_sat. apply Z.leb_le. Qed.

Definition models (v : nvaluation) (G : list edge) : Prop := Forall (edge_sat v) G.

Definition nodes (G : list edge) : list node :=
  nodup node_eq_dec (NZero :: flat_map (fun e => [e_src e; e_dst e]) G).

(** ** Models *)

Definition model : Type := list (node * Z).

Definition val_of (m : model) : nvaluation :=
  fun a => match find (fun p => node_eqb (fst p) a) m with Some (_, z) => z | None => 0 end.

Definition check_model (G : list edge) (m : model) : bool := forallb (edge_satb (val_of m)) G.

Lemma check_model_sound : forall G m, check_model G m = true -> models (val_of m) G.
Proof.
  intros G m H. apply Forall_forall. intros e He. unfold check_model in H.
  rewrite forallb_forall in H. apply edge_satb_sat, H, He.
Qed.

(** ** Cycles *)

Fixpoint chain_ok (x : node) (c : list edge) (y : node) : bool :=
  match c with
  | [] => node_eqb x y
  | e :: c' => node_eqb x (e_src e) && chain_ok (e_dst e) c' y
  end.

Definition weight (c : list edge) : Z := fold_right (fun e z => e_w e + z) 0 c.

Definition mem_edge (G : list edge) (e : edge) : bool :=
  existsb (fun f => if edge_eq_dec e f then true else false) G.

Definition cycle_ok (G : list edge) (c : list edge) : bool :=
  match c with
  | [] => false
  | e :: _ => chain_ok (e_src e) c (e_src e) && (0 <? weight c) && forallb (mem_edge G) c
  end.

Lemma chain_ok_sum : forall v c x y, chain_ok x c y = true -> Forall (edge_sat v) c ->
  aval v x + weight c <= aval v y.
Proof.
  intros v c. induction c as [|e c IH]; intros x y H Hs; cbn in H.
  - apply node_eqb_eq in H. subst. cbn. lia.
  - apply andb_prop in H as [H1 H2]. apply node_eqb_eq in H1. subst.
    inversion Hs as [|? ? He Hc]; subst. specialize (IH _ _ H2 Hc).
    unfold edge_sat in He. change (weight (e :: c)) with (e_w e + weight c). lia.
Qed.

Theorem cycle_ok_sound : forall G c, cycle_ok G c = true -> forall v, ~ models v G.
Proof.
  intros G c H v Hv. destruct c as [|e c']; [discriminate H | ].
  unfold cycle_ok in H. apply andb_prop in H as [H Hm]. apply andb_prop in H as [Hc Hw].
  apply Z.ltb_lt in Hw.
  assert (Hs : Forall (edge_sat v) (e :: c')).
  { apply Forall_forall. intros f Hf. rewrite forallb_forall in Hm. specialize (Hm f Hf).
    unfold mem_edge in Hm. apply existsb_exists in Hm as (g & Hg & Heq).
    destruct (edge_eq_dec f g) as [-> | ]; [ | discriminate Heq].
    unfold models in Hv. rewrite Forall_forall in Hv. exact (Hv g Hg). }
  pose proof (chain_ok_sum v _ _ _ Hc Hs). lia.
Qed.

(** ** Bellman–Ford for the longest paths *)

Definition dists : Type := list (node * Z).
Definition preds : Type := list (node * edge).

Fixpoint dget (d : dists) (a : node) : Z :=
  match d with [] => 0 | (b, z) :: d' => if node_eqb a b then z else dget d' a end.

Fixpoint pget (p : preds) (a : node) : option edge :=
  match p with [] => None | (b, e) :: p' => if node_eqb a b then Some e else pget p' a end.

Definition violated (d : dists) (e : edge) : bool := dget d (e_dst e) <? dget d (e_src e) + e_w e.

Definition relax_one (st : dists * preds) (e : edge) : dists * preds :=
  let (d, p) := st in
  if violated d e then ((e_dst e, dget d (e_src e) + e_w e) :: d, (e_dst e, e) :: p) else st.

Fixpoint rounds (n : nat) (es : list edge) (st : dists * preds) : dists * preds :=
  match n with
  | O => st
  | S n' => rounds n' es (fold_left relax_one es st)
  end.

(** [walk] goes [n] steps back along the predecessors; [collect] then
    gathers the cycle through the node reached, in the order of the
    edges. *)
Fixpoint walk (p : preds) (n : nat) (x : node) : node :=
  match n with
  | O => x
  | S n' => match pget p x with Some e => walk p n' (e_src e) | None => x end
  end.

Fixpoint collect (p : preds) (n : nat) (x y : node) (acc : list edge) : option (list edge) :=
  match n with
  | O => None
  | S n' =>
      match pget p y with
      | None => None
      | Some e => if node_eqb (e_src e) x then Some (e :: acc) else collect p n' x (e_src e) (e :: acc)
      end
  end.

Inductive gverdict : Type :=
| GModel : model -> gverdict
| GCycle : list edge -> gverdict
| GUnknown : gverdict.

Definition solve (G : list edge) : gverdict :=
  let n := length (nodes G) in
  let (d, p) := rounds n G ([], []) in
  match find (violated d) G with
  | None =>
      let m := map (fun x => (x, dget d x - dget d NZero)) (nodes G) in
      if check_model G m then GModel m else GUnknown
  | Some e =>
      let p' := (e_dst e, e) :: p in
      let x := walk p' n (e_dst e) in
      match collect p' (S n) x x [] with
      | Some c => if cycle_ok G c then GCycle c else GUnknown
      | None => GUnknown
      end
  end.

Theorem solve_model : forall G m, solve G = GModel m -> models (val_of m) G.
Proof.
  intros G m H. unfold solve in H.
  destruct (rounds _ _ _) as [d p].
  destruct (find (violated d) G) as [e|].
  - destruct (collect _ _ _ _ _) as [c|]; [ | discriminate H].
    destruct (cycle_ok G c); discriminate H.
  - match type of H with (if check_model G ?m0 then _ else _) = _ => destruct (check_model G m0) eqn:E end;
      [ | discriminate H].
    injection H as <-. exact (check_model_sound _ _ E).
Qed.

Theorem solve_cycle : forall G c, solve G = GCycle c -> cycle_ok G c = true.
Proof.
  intros G c H. unfold solve in H.
  destruct (rounds _ _ _) as [d p].
  destruct (find (violated d) G) as [e|].
  - destruct (collect _ _ _ _ _) as [c'|]; [ | discriminate H].
    destruct (cycle_ok G c') eqn:E; [ | discriminate H].
    injection H as <-. exact E.
  - match type of H with (if ?b then _ else _) = _ => destruct b end; discriminate H.
Qed.

Corollary solve_cycle_unsat : forall G c, solve G = GCycle c -> forall v, ~ models v G.
Proof. intros G c H. exact (cycle_ok_sound G c (solve_cycle G c H)). Qed.

(** ** Entailment *)

Definition negate (e : edge) : edge := (e_dst e, 1 - e_w e, e_src e).

Inductive entailment : Type :=
| Entailed : list edge -> entailment   (** the cycle of the graph with the negation *)
| Countered : model -> entailment      (** a model of the graph violating the edge *)
| EUnknown : entailment.

Definition entails (G : list edge) (e : edge) : entailment :=
  match solve (negate e :: G) with
  | GCycle c => Entailed c
  | GModel m => Countered m
  | GUnknown => EUnknown
  end.

(** The certificate of an entailment, checked on its own. *)
Definition entailment_ok (G : list edge) (e : edge) (c : list edge) : bool := cycle_ok (negate e :: G) c.

Lemma entailment_ok_sound : forall G e c, entailment_ok G e c = true ->
  forall v, models v G -> edge_sat v e.
Proof.
  intros G e c H v Hv. pose proof (cycle_ok_sound _ _ H v) as Hn. unfold edge_sat in *.
  destruct (Z_le_gt_dec (aval v (e_src e) + e_w e) (aval v (e_dst e))) as [Hle | Hgt]; [exact Hle | ].
  exfalso. apply Hn. constructor; [ | exact Hv].
  unfold edge_sat, negate; cbn [e_src e_w e_dst]. lia.
Qed.

Theorem entails_entailed : forall G e c, entails G e = Entailed c ->
  entailment_ok G e c = true.
Proof.
  intros G e c H. unfold entails in H.
  destruct (solve (negate e :: G)) eqn:E; try discriminate H. injection H as <-.
  exact (solve_cycle _ _ E).
Qed.

Theorem entails_countered : forall G e m, entails G e = Countered m ->
  models (val_of m) G /\ ~ edge_sat (val_of m) e.
Proof.
  intros G e m H. unfold entails in H.
  destruct (solve (negate e :: G)) eqn:E; try discriminate H. injection H as <-.
  pose proof (solve_model _ _ E) as Hm. inversion Hm as [|? ? Hn HG]; subst.
  split; [exact HG | ]. unfold edge_sat, negate in *; cbn [e_src e_w e_dst] in Hn. lia.
Qed.
