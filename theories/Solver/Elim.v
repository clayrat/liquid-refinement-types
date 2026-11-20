(** * Elimination of equalities

    A step before the classification of atoms (Solver/Prove.v).  A
    hypothesis [t₁ = t₂] whose linear form [t₁ − t₂] has the coefficient
    [±1] at a node [x] — an integer variable or [len a] — is solved for
    it, [x = s], and [s] is substituted for [x] in the other hypotheses
    and in the goal; [lin] collects like terms afterwards.  So
    [d = y − x] with the goal [d > 0] gives the difference atom
    [y − x > 0], and the goal of the branch [cons] of [append] becomes
    [0 = 0] whatever the order of the summands in the contract
    (Examples/Append.v).  Neither needs a solver of linear arithmetic.

    An elimination of [len a] keeps [0 ≤ s] as a hypothesis: the length
    is non-negative in every valuation the obligation quantifies over,
    and the node [len a], with its edge [0 ≤ len a], is gone.

    A step is a pair [(x, s)].  [elim_step] checks it — some hypothesis,
    solved for [x], gives exactly [s] — and applies it; [reduce] applies a
    list of steps to an obligation whose hypotheses are split into
    conjuncts.  [reduce_sound]: if the reduced obligation is valid, so is
    the original.  This is the theorem that keeps [Proved] a checked
    answer: the steps are a part of the certificate, and the checker
    applies them itself.

    [elims_of] chooses the steps: repeatedly the first hypothesis that is
    an equality with a coefficient [±1], at its first such node.
    [back_subst] extends a model of the reduced obligation by the values
    of the eliminated nodes, last step first; the result is checked on
    the original obligation like any counter-model. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula Obligation.
From Liquid.Solver Require Import Diff Linear.

Local Open Scope Z_scope.

(** ** Substituting a term for a node *)

Fixpoint tsubst_node (n : node) (s : term) (t : term) : term :=
  match t with
  | TVar x => if node_eqb n (NInt x) then s else t
  | TLen a => if node_eqb n (NLen a) then s else t
  | TConst _ => t
  | TAdd t1 t2 => TAdd (tsubst_node n s t1) (tsubst_node n s t2)
  | TSub t1 t2 => TSub (tsubst_node n s t1) (tsubst_node n s t2)
  | TMul k t1 => TMul k (tsubst_node n s t1)
  end.

Definition asubst_node (n : node) (s : term) (u : arg) : arg :=
  match u with UInt t => UInt (tsubst_node n s t) | UBool _ => u end.

Fixpoint fsubst_node (n : node) (s : term) (p : formula) : formula :=
  match p with
  | FLe t1 t2 => FLe (tsubst_node n s t1) (tsubst_node n s t2)
  | FLt t1 t2 => FLt (tsubst_node n s t1) (tsubst_node n s t2)
  | FEq t1 t2 => FEq (tsubst_node n s t1) (tsubst_node n s t2)
  | FAtom _ => p
  | FKappa k us => FKappa k (map (asubst_node n s) us)
  | FAnd p q => FAnd (fsubst_node n s p) (fsubst_node n s q)
  | FOr p q => FOr (fsubst_node n s p) (fsubst_node n s q)
  | FNot p => FNot (fsubst_node n s p)
  end.

Lemma tsubst_node_eval : forall ρ n s t, aval (nval ρ) n = teval ρ s ->
  teval ρ (tsubst_node n s t) = teval ρ t.
Proof.
  intros ρ n s t H. induction t; cbn [tsubst_node teval]; try reflexivity; try lia.
  - destruct (node_eqb n (NInt x)) eqn:E; [ | reflexivity].
    apply node_eqb_eq in E. subst n. cbn in H. cbn. lia.
  - destruct (node_eqb n (NLen a)) eqn:E; [ | reflexivity].
    apply node_eqb_eq in E. subst n. cbn in H. cbn. lia.
Qed.

Lemma fsubst_node_holds : forall ki ρ n s p, aval (nval ρ) n = teval ρ s ->
  holds ki ρ (fsubst_node n s p) <-> holds ki ρ p.
Proof.
  intros ki ρ n s p H. induction p; cbn [fsubst_node holds]; rewrite ?(tsubst_node_eval ρ n s _ H); try tauto.
  rewrite map_map. replace (map (fun u => aeval ρ (asubst_node n s u)) us) with (map (aeval ρ) us); [tauto | ].
  apply map_ext. intros [t | b]; cbn; [now rewrite (tsubst_node_eval ρ n s t H) | reflexivity].
Qed.

(** ** Solving an equality for a node *)

Definition term_node (n : node) : option term :=
  match n with NInt x => Some (TVar x) | NLen a => Some (TLen a) | _ => None end.

Lemma term_node_eval : forall ρ n t, term_node n = Some t -> teval ρ t = aval (nval ρ) n.
Proof. intros ρ [ | x | b | a] t H; cbn in H; try discriminate H; injection H as <-; reflexivity. Qed.

Definition coef_of (n : node) (cs : list (node * Z)) : Z :=
  fold_right (fun p acc => if node_eqb (fst p) n then snd p + acc else acc) 0 cs.

Definition drop_node (n : node) (cs : list (node * Z)) : list (node * Z) :=
  filter (fun p => negb (node_eqb (fst p) n)) cs.

Lemma lsum_split : forall v n cs, lsum v cs = coef_of n cs * aval v n + lsum v (drop_node n cs).
Proof.
  intros v n cs. induction cs as [|[m d] cs IH]; [reflexivity | ].
  unfold coef_of, drop_node in *. cbn [fold_right filter fst snd lsum].
  destruct (node_eqb m n) eqn:E; cbn [negb lsum].
  - apply node_eqb_eq in E. subst m. rewrite IH. ring.
  - rewrite IH. ring.
Qed.

(** The term of a linear form: [c·x] as [x] for [c = 1], a positive
    coefficient added, a negative one subtracted, the constant last. *)
Definition mono (c : Z) (t : term) : term := if c =? 1 then t else TMul c t.

Fixpoint lin_term (acc : term) (cs : list (node * Z)) : option term :=
  match cs with
  | [] => Some acc
  | (n, c) :: cs' =>
      match term_node n with
      | Some t => lin_term (if 0 <? c then TAdd acc (mono c t) else TSub acc (mono (- c) t)) cs'
      | None => None
      end
  end.

Definition term_of_lin (l : linform) : option term :=
  let (cs, k) := l in
  match cs with
  | [] => Some (TConst k)
  | (n, c) :: cs' =>
      match term_node n with
      | Some t =>
          match lin_term (mono c t) cs' with
          | Some acc =>
              Some (if k =? 0 then acc else if 0 <? k then TAdd acc (TConst k) else TSub acc (TConst (- k)))
          | None => None
          end
      | None => None
      end
  end.

Lemma mono_eval : forall ρ c t, teval ρ (mono c t) = c * teval ρ t.
Proof. intros ρ c t. unfold mono. destruct (Z.eqb_spec c 1); cbn; lia. Qed.

Lemma lin_term_eval : forall ρ cs acc s, lin_term acc cs = Some s ->
  teval ρ s = teval ρ acc + lsum (nval ρ) cs.
Proof.
  intros ρ cs. induction cs as [|[n c] cs IH]; intros acc s H; cbn in H |- *.
  - injection H as <-. lia.
  - destruct (term_node n) as [t | ] eqn:Et; [ | discriminate H].
    rewrite (IH _ _ H). rewrite <- (term_node_eval ρ n t Et).
    destruct (Z.ltb_spec 0 c); cbn; rewrite mono_eval; lia.
Qed.

Lemma term_of_lin_eval : forall ρ l s, term_of_lin l = Some s -> teval ρ s = leval (nval ρ) l.
Proof.
  intros ρ [cs k] s H. unfold leval. cbn [fst snd]. unfold term_of_lin in H.
  destruct cs as [|[n c] cs].
  - injection H as <-. cbn. lia.
  - destruct (term_node n) as [t | ] eqn:Et; [ | discriminate H].
    destruct (lin_term (mono c t) cs) as [acc | ] eqn:Ea; [ | discriminate H]. injection H as <-.
    pose proof (lin_term_eval ρ cs _ _ Ea) as Hacc. rewrite mono_eval, (term_node_eval ρ n t Et) in Hacc.
    cbn [lsum].
    destruct (Z.eqb_spec k 0); [ | destruct (Z.ltb_spec 0 k)]; cbn; lia.
Qed.

Definition is_unit (c : Z) : bool := (c =? 1) || (c =? -1).

(** [x = s] from [t₁ = t₂]: the coefficient [c = ±1] of [x] in
    [t₁ − t₂ = c·x + r], and [s = −c·r]. *)
Definition solve_for (n : node) (h : formula) : option term :=
  match h with
  | FEq t1 t2 =>
      let l := lin (TSub t1 t2) in
      let c := coef_of n (fst l) in
      match term_node n with
      | Some _ =>
          if is_unit c
          then term_of_lin (map (fun p => (fst p, - c * snd p)) (drop_node n (fst l)), - c * snd l)
          else None
      | None => None
      end
  | _ => None
  end.

Lemma solve_for_sound : forall ki ρ n h s, solve_for n h = Some s -> holds ki ρ h ->
  aval (nval ρ) n = teval ρ s.
Proof.
  intros ki ρ n h s H Hh. destruct h as [ | | t1 t2 | | | | | ]; try discriminate H.
  unfold solve_for in H. cbv zeta in H.
  pose proof (lin_sound ρ (TSub t1 t2)) as Hl.
  destruct (lin (TSub t1 t2)) as [cs k]. cbn [fst snd] in H.
  destruct (term_node n) as [tn | ]; [ | discriminate H].
  destruct (is_unit (coef_of n cs)) eqn:Eu; [ | discriminate H].
  cbn [holds] in Hh. cbn [teval] in Hl.
  rewrite (term_of_lin_eval ρ _ s H). unfold leval in *. cbn [fst snd] in *.
  rewrite lsum_scale.
  rewrite (lsum_split (nval ρ) n cs) in Hl.
  unfold is_unit in Eu. apply orb_true_iff in Eu as [Eu | Eu]; apply Z.eqb_eq in Eu; rewrite Eu in *; lia.
Qed.

(** ** A step and its check *)

Definition elim : Type := (node * term)%type.

Definition defines (n : node) (s : term) (h : formula) : bool :=
  match solve_for n h with
  | Some s' => if term_eq_dec s s' then true else false
  | None => false
  end.

(** The hypotheses without the first one that, solved for [x], gives [s]. *)
Fixpoint take_def (n : node) (s : term) (hs : list formula) : option (list formula) :=
  match hs with
  | [] => None
  | h :: hs' =>
      if defines n s h then Some hs'
      else match take_def n s hs' with Some r => Some (h :: r) | None => None end
  end.

Lemma take_def_spec : forall n s hs hs', take_def n s hs = Some hs' ->
  exists h, In h hs /\ solve_for n h = Some s /\ (forall p, In p hs' -> In p hs).
Proof.
  intros n s hs. induction hs as [|h hs IH]; intros hs' H; cbn in H; [discriminate H | ].
  destruct (defines n s h) eqn:Ed.
  - injection H as <-. exists h. split; [now left | split; [ | intros p Hp; now right]].
    unfold defines in Ed. destruct (solve_for n h) as [s' | ]; [ | discriminate Ed].
    destruct (term_eq_dec s s'); [now subst | discriminate Ed].
  - destruct (take_def n s hs) as [r | ] eqn:Er; [ | discriminate H]. injection H as <-.
    destruct (IH r eq_refl) as (h' & Hin & Hs & Hr).
    exists h'. split; [now right | split; [exact Hs | ]].
    intros p [<- | Hp]; [now left | right; exact (Hr p Hp)].
Qed.

(** An eliminated length stays non-negative. *)
Definition nonneg_of (n : node) (s : term) : list formula :=
  match n with NLen _ => [FLe (TConst 0) s] | _ => [] end.

Definition elim_step (st : elim) (hs : list formula) (g : formula) : option (list formula * formula) :=
  let (n, s) := st in
  match take_def n s hs with
  | Some hs' => Some (map (fsubst_node n s) hs' ++ nonneg_of n s, fsubst_node n s g)
  | None => None
  end.

Fixpoint elim_steps (els : list elim) (hs : list formula) (g : formula) : option (list formula * formula) :=
  match els with
  | [] => Some (hs, g)
  | st :: els' =>
      match elim_step st hs g with
      | Some (hs', g') => elim_steps els' hs' g'
      | None => None
      end
  end.

Definition reduce (els : list elim) (ob : obligation) : option obligation :=
  match elim_steps els (flat_map conjuncts (ob_hyps ob)) (ob_goal ob) with
  | Some (hs, g) => Some (mkOb (ob_label ob) hs g)
  | None => None
  end.

Lemma elim_step_sound : forall st hs g hs' g', elim_step st hs g = Some (hs', g') ->
  forall ki ρ, lens_nonneg ρ -> Forall (holds ki ρ) hs ->
  Forall (holds ki ρ) hs' /\ (holds ki ρ g' -> holds ki ρ g).
Proof.
  intros [n s] hs g hs' g' H ki ρ Hl Hh. cbn in H.
  destruct (take_def n s hs) as [r | ] eqn:Et; [ | discriminate H]. injection H as <- <-.
  destruct (take_def_spec n s hs r Et) as (h & Hin & Hs & Hr).
  pose proof (solve_for_sound ki ρ n h s Hs (proj1 (Forall_forall _ _) Hh h Hin)) as Hn.
  split.
  - apply Forall_app. split.
    + apply Forall_forall. intros q Hq. apply in_map_iff in Hq as (p & <- & Hp).
      apply (fsubst_node_holds ki ρ n s p Hn). exact (proj1 (Forall_forall _ _) Hh p (Hr p Hp)).
    + destruct n as [ | x | b | a]; cbn; repeat constructor.
      cbn in Hn |- *. specialize (Hl a). lia.
  - apply (fsubst_node_holds ki ρ n s g Hn).
Qed.

Lemma elim_steps_sound : forall els hs g hs' g', elim_steps els hs g = Some (hs', g') ->
  forall ki ρ, lens_nonneg ρ -> Forall (holds ki ρ) hs ->
  Forall (holds ki ρ) hs' /\ (holds ki ρ g' -> holds ki ρ g).
Proof.
  intros els. induction els as [|st els IH]; intros hs g hs' g' H ki ρ Hl Hh; cbn in H.
  - injection H as <- <-. auto.
  - destruct (elim_step st hs g) as [[hs1 g1] | ] eqn:E; [ | discriminate H].
    destruct (elim_step_sound st hs g hs1 g1 E ki ρ Hl Hh) as [H1 G1].
    destruct (IH hs1 g1 hs' g' H ki ρ Hl H1) as [H2 G2]. auto.
Qed.

Theorem reduce_sound : forall els ob ob', reduce els ob = Some ob' -> valid ob' -> valid ob.
Proof.
  intros els ob ob' H Hv ki ρ Hl Hh. unfold reduce in H.
  destruct (elim_steps els (flat_map conjuncts (ob_hyps ob)) (ob_goal ob)) as [[hs g] | ] eqn:E;
    [ | discriminate H].
  injection H as <-.
  assert (Hc : Forall (holds ki ρ) (flat_map conjuncts (ob_hyps ob))).
  { apply Forall_forall. intros q Hq. apply in_flat_map in Hq as (h & Hh' & Hq).
    pose proof (proj1 (holds_conjuncts ki ρ h) (proj1 (Forall_forall _ _) Hh h Hh')) as Hcj.
    exact (proj1 (Forall_forall _ _) Hcj q Hq). }
  destruct (elim_steps_sound els _ _ hs g E ki ρ Hl Hc) as [H1 G1].
  apply G1. exact (Hv ki ρ Hl H1).
Qed.

(** ** Choosing the steps *)

Fixpoint first_some {A B} (f : A -> option B) (l : list A) : option B :=
  match l with
  | [] => None
  | a :: l' => match f a with Some b => Some b | None => first_some f l' end
  end.

(** The first node of an equality that it can be solved for. *)
Definition def_of (h : formula) : option elim :=
  match h with
  | FEq t1 t2 =>
      first_some (fun p => match solve_for (fst p) h with Some s => Some (fst p, s) | None => None end)
                 (fst (lin (TSub t1 t2)))
  | _ => None
  end.

Fixpoint find_elims (fuel : nat) (hs : list formula) (g : formula) : list elim :=
  match fuel with
  | O => []
  | S fuel' =>
      match first_some def_of hs with
      | Some st =>
          match elim_step st hs g with
          | Some (hs', g') => st :: find_elims fuel' hs' g'
          | None => []
          end
      | None => []
      end
  end.

(** Every step removes an equality and adds none: as many steps as
    hypotheses suffice. *)
Definition elims_of (ob : obligation) : list elim :=
  let hs := flat_map conjuncts (ob_hyps ob) in
  find_elims (length hs) hs (ob_goal ob).

(** ** Back to the original names *)

Definition cm_extend (st : elim) (m : cmodel) : cmodel :=
  let z := teval (val_of_cmodel m) (snd st) in
  match fst st with
  | NInt x => mkCModel (cm_int m ++ [(x, z)]) (cm_bool m) (cm_len m)
  | NLen a => mkCModel (cm_int m) (cm_bool m) (cm_len m ++ [(a, z)])
  | _ => m
  end.

Definition back_subst (els : list elim) (m : cmodel) : cmodel := fold_right cm_extend m els.
