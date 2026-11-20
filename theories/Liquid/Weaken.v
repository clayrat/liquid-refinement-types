(** * Iterative weakening

    Every unknown [κ] has a signature of sorted formal parameters and a
    finite list of qualifiers [Qκ] over them; a solution maps it to the
    qualifiers still kept, read as their conjunction ([true] for none).

      for every κ:  Sκ := Qκ
      repeat until stable:
        for every constraint A ⊢ κ(ū), in the order of the list:
          substitute the current conjunctions for the unknowns in A
          for every q in Sκ:
            check A ⊢ q[ū]
            Proved: keep q;  Refuted: remove q;  Unknown: answer Undecided
      check every constraint with a fixed goal

    The qualifiers of a constraint are checked against [A] with the
    solution at the start of that constraint; a removal can widen the
    hypotheses of other constraints, so the round is repeated until no
    qualifier is removed.  The trace ([wevent]) records, for every
    constraint with an unknown goal, the qualifiers removed with their
    obligations and counter-models, and the qualifiers left.

    The fuel is [1 + Σ|Qκ|]: every round that is not stable removes at
    least one qualifier, so the fuel is enough and [WOutOfFuel] never
    happens ([weaken_fuel_enough]).  For constraints of the shape of
    [horn_of] ([horn_ok]) and qualifiers without unknowns, every
    obligation passed to the oracle is without unknowns
    ([weaken_kfree_queries]).  That the result is the strongest
    solution in [Q] and does not depend on the order of the constraints
    are open obligations (Contracts.v).  The result is not trusted: the
    caller (Liquid/Infer.v) substitutes it into the contracts and checks
    them again with the first algorithm.

    Independent of the programs (Lang/). *)

From Stdlib Require Import String List Bool Arith Lia.
Import ListNotations.
From Liquid.Common Require Import Result Traced.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Liquid Require Import Horn.

Local Open Scope string_scope.
Local Open Scope list_scope.

Record kdecl : Type := mkKDecl {
  kd_name : string;
  kd_formals : list (string * sort);
  kd_quals : list formula
}.

Definition solution : Type := list (string * list formula).

Definition kfind (D : list kdecl) (k : string) : option kdecl :=
  find (fun d => String.eqb (kd_name d) k) D.

(** A qualifier of [κ] at the arguments [ū]. *)
Definition kinst (d : kdecl) (us : list arg) (q : formula) : formula := fsubst (ksubst (kd_formals d) us) q.

(** The solution substituted for the unknowns of a formula. *)
Fixpoint apply_sol (D : list kdecl) (sol : solution) (p : formula) : formula :=
  match p with
  | FKappa k us =>
      match kfind D k, assoc k sol with
      | Some d, Some qs => fconj (map (kinst d us) qs)
      | _, _ => p
      end
  | FAnd p q => fand (apply_sol D sol p) (apply_sol D sol q)
  | FOr p q => FOr (apply_sol D sol p) (apply_sol D sol q)
  | FNot p => FNot (apply_sol D sol p)
  | _ => p
  end.

Fixpoint update (k : string) (qs : list formula) (sol : solution) : solution :=
  match sol with
  | [] => []
  | (k', qs') :: sol' => if String.eqb k k' then (k', qs) :: sol' else (k', qs') :: update k qs sol'
  end.

Fixpoint size (sol : solution) : nat :=
  match sol with
  | [] => 0
  | (_, qs) :: sol' => length qs + size sol'
  end.

Inductive wevent : Type :=
| WRound (n : nat)
| WStep (l : label) (k : string) (removed : list (formula * obligation * cmodel)) (kept : list formula).

Inductive wfail : Type :=
| WUndecided (ob : obligation) (why : string)
| WRefuted (ob : obligation) (m : cmodel)
| WUnknownKappa (k : string)
| WOutOfFuel.

Section Weaken.
  Context {C : Type} (oracle : obligation -> verdict C).
  Variable D : list kdecl.

  Fixpoint filter_quals (A : list formula) (l : label) (d : kdecl) (us : list arg) (qs : list formula)
    : result wfail (list formula * list (formula * obligation * cmodel)) :=
    match qs with
    | [] => Ok ([], [])
    | q :: qs' =>
        let ob := mkOb l A (kinst d us q) in
        match oracle ob with
        | Proved _ =>
            let* r := filter_quals A l d us qs' in
            Ok (q :: fst r, snd r)
        | Refuted m =>
            let* r := filter_quals A l d us qs' in
            Ok (fst r, (q, ob, m) :: snd r)
        | Unknown why => Err (WUndecided ob why)
        end
    end.

  Definition step (sol : solution) (h : horn) : traced wevent wfail (solution * bool) :=
    match h_goal h with
    | HFixed _ => tret (sol, false)
    | HKappa k us =>
        match kfind D k, assoc k sol with
        | Some d, Some qs =>
            let A := map (apply_sol D sol) (h_hyps h) in
            match filter_quals A (h_label h) d us qs with
            | Ok (kept, removed) =>
                let! _ := temit (WStep (h_label h) k removed kept) in
                tret (update k kept sol, match removed with [] => false | _ => true end)
            | Err e => tfail e
            end
        | _, _ => tfail (WUnknownKappa k)
        end
    end.

  Fixpoint round (sol : solution) (hs : list horn) (changed : bool) : traced wevent wfail (solution * bool) :=
    match hs with
    | [] => tret (sol, changed)
    | h :: hs' =>
        let! r := step sol h in
        round (fst r) hs' (changed || snd r)
    end.

  Fixpoint iterate (fuel n : nat) (sol : solution) (hs : list horn) : traced wevent wfail solution :=
    match fuel with
    | O => tfail WOutOfFuel
    | S f =>
        let! _ := temit (WRound n) in
        let! r := round sol hs false in
        if snd r then iterate f (S n) (fst r) hs else tret (fst r)
    end.

  Definition fixed_ob (sol : solution) (h : horn) (p : formula) : obligation :=
    mkOb (h_label h) (map (apply_sol D sol) (h_hyps h)) p.

  Definition check_fixed (sol : solution) (hs : list horn) : traced wevent wfail unit :=
    titer (fun h =>
             match h_goal h with
             | HFixed p =>
                 let ob := fixed_ob sol h p in
                 match oracle ob with
                 | Proved _ => tret tt
                 | Refuted m => tfail (WRefuted ob m)
                 | Unknown why => tfail (WUndecided ob why)
                 end
             | HKappa _ _ => tret tt
             end) hs.

  Definition initial (D : list kdecl) : solution := map (fun d => (kd_name d, kd_quals d)) D.

  Definition weaken (hs : list horn) : traced wevent wfail solution :=
    let sol0 := initial D in
    let! sol := iterate (S (size sol0)) 1 sol0 hs in
    let! _ := check_fixed sol hs in
    tret sol.

  (** ** The fuel is enough *)

  Lemma filter_quals_length : forall A l d us qs kept removed,
    filter_quals A l d us qs = Ok (kept, removed) -> length kept + length removed = length qs.
  Proof.
    intros A l d us qs. induction qs as [|q qs IH]; intros kept removed H; cbn in H.
    - injection H as <- <-. reflexivity.
    - destruct (oracle _); [ | | discriminate H].
      + bind_in H r Hr. injection H as <- <-. destruct r as [k' r']. cbn. rewrite (IH _ _ Hr). reflexivity.
      + bind_in H r Hr. injection H as <- <-. destruct r as [k' r']. cbn. specialize (IH _ _ Hr). lia.
  Qed.

  Lemma update_size : forall k qs sol old, assoc k sol = Some old ->
    size (update k qs sol) + length old = size sol + length qs.
  Proof.
    intros k qs sol. induction sol as [|[k' qs'] sol IH]; intros old H; cbn in H; [discriminate H | ].
    cbn. destruct (String.eqb k k'); [injection H as <-; cbn; lia | ].
    cbn. specialize (IH old H). lia.
  Qed.

  Lemma step_size : forall sol h log log' sol' b,
    step sol h log = (log', Ok (sol', b)) -> size sol' <= size sol /\ (b = false \/ size sol' < size sol).
  Proof.
    intros sol h log log' sol' b H. unfold step in H.
    destruct (h_goal h) as [k us | p]; [ | injection H as _ <- <-; lia].
    destruct (kfind D k) as [d | ]; [ | discriminate H].
    destruct (assoc k sol) as [qs | ] eqn:Ea; [ | discriminate H].
    destruct (filter_quals _ _ _ _ _) as [[kept removed] | e] eqn:Ef; [ | discriminate H].
    cbn in H. injection H as _ <- <-.
    pose proof (filter_quals_length _ _ _ _ _ _ _ Ef) as Hl.
    pose proof (update_size k kept sol qs Ea) as Hu.
    destruct removed; cbn in Hl; (split; [lia | ]); [left; reflexivity | right; lia].
  Qed.

  Lemma round_size : forall hs sol changed log log' sol' b,
    round sol hs changed log = (log', Ok (sol', b)) ->
    size sol' <= size sol /\ (b = changed \/ size sol' < size sol).
  Proof.
    intros hs. induction hs as [|h hs IH]; intros sol changed log log' sol' b H; cbn in H.
    - injection H as _ <- <-. split; [lia | left; reflexivity].
    - apply tbind_ok in H as (log1 & [s1 b1] & Hs & H). cbn in H.
      destruct (step_size _ _ _ _ _ _ Hs) as [Hle1 Hb1].
      destruct (IH _ _ _ _ _ _ H) as [Hle2 Hb2].
      split; [lia | ].
      destruct Hb2 as [-> | Hlt]; [ | right; lia].
      destruct Hb1 as [-> | Hlt]; [left; destruct changed; reflexivity | right; lia].
  Qed.

  Lemma round_fail : forall hs sol changed log log' e,
    round sol hs changed log = (log', Err e) -> e <> WOutOfFuel.
  Proof.
    intros hs. induction hs as [|h hs IH]; intros sol changed log log' e H; cbn in H; [discriminate H | ].
    unfold tbind in H. destruct (step sol h log) as [log1 [[s1 b1] | e1]] eqn:Es.
    - exact (IH _ _ _ _ _ H).
    - injection H as _ ->. unfold step in Es.
      destruct (h_goal h) as [k us | p]; [ | discriminate Es].
      destruct (kfind D k); [ | injection Es as _ <-; discriminate].
      destruct (assoc k sol); [ | injection Es as _ <-; discriminate].
      destruct (filter_quals _ _ _ _ _) as [[kept removed] | e2] eqn:Ef; [discriminate Es | ].
      injection Es as _ <-.
      clear -Ef. revert Ef. generalize (h_hyps h). intros hyps.
      induction l as [|q qs IHq]; cbn; intros Ef; [discriminate Ef | ].
      destruct (oracle _); [ | | injection Ef as <-; discriminate].
      + destruct (filter_quals _ _ _ _ qs) eqn:E'; cbn in Ef; [discriminate Ef | injection Ef as <-; auto].
      + destruct (filter_quals _ _ _ _ qs) eqn:E'; cbn in Ef; [discriminate Ef | injection Ef as <-; auto].
  Qed.

  Lemma iterate_fuel : forall fuel n sol hs log log' e,
    size sol < fuel -> iterate fuel n sol hs log = (log', Err e) -> e <> WOutOfFuel.
  Proof.
    induction fuel as [|f IH]; intros n sol hs log log' e Hs H; [lia | ].
    cbn in H. unfold tbind at 1 in H. cbn in H. unfold tbind in H.
    destruct (round sol hs false (WRound n :: log)) as [log1 [[s1 b1] | e1]] eqn:Er.
    - destruct (round_size _ _ _ _ _ _ _ Er) as [Hle Hb]. destruct b1.
      + destruct Hb as [Hb | Hlt]; [discriminate Hb | ]. eapply IH; [ | exact H]. cbn. lia.
      + discriminate H.
    - injection H as _ <-. exact (round_fail _ _ _ _ _ _ Er).
  Qed.

  Lemma check_fixed_fail : forall sol hs log log' e,
    check_fixed sol hs log = (log', Err e) -> e <> WOutOfFuel.
  Proof.
    intros sol hs. unfold check_fixed. induction hs as [|h hs IH]; intros log log' e H; cbn in H; [discriminate H | ].
    unfold tbind in H.
    destruct (h_goal h) as [k us | p].
    - exact (IH _ _ _ H).
    - destruct (oracle (fixed_ob sol h p)); cbn in H; [exact (IH _ _ _ H) | injection H as _ <-; discriminate
                                                      | injection H as _ <-; discriminate].
  Qed.

  Theorem weaken_fuel_enough : forall hs log log' e, weaken hs log = (log', Err e) -> e <> WOutOfFuel.
  Proof.
    intros hs log log' e H. unfold weaken in H. unfold tbind in H.
    destruct (iterate _ _ _ _ log) as [log1 [sol | e1]] eqn:Ei.
    - destruct (check_fixed sol hs log1) as [log2 [u | e2]] eqn:Ec; [discriminate H | ].
      injection H as _ <-. exact (check_fixed_fail _ _ _ _ _ Ec).
    - injection H as _ <-. eapply iterate_fuel; [ | exact Ei]. lia.
  Qed.
End Weaken.

(** ** Weakening asks only obligations without unknowns

    Under the shape of the constraints [horn_of] gives ([horn_ok]) and
    with qualifiers without unknowns ([quals_kfree]), every obligation
    weakening passes to the oracle is without unknowns: the solution
    substituted into the hypotheses replaces every unknown, and the goals
    are qualifiers or fixed goals without unknowns.  Hence two oracles
    that agree on such obligations give the same run, the trace included
    ([weaken_kfree_queries]), and a completeness of the oracle on them
    ([oracle_complete]) is all weakening can rely on. *)

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

Definition quals_kfree (D : list kdecl) : Prop :=
  Forall (fun d => Forall (fun q => kfree q = true) (kd_quals d)) D.

(** The invariant of the solution: the unknowns of [D], each with
    qualifiers without unknowns. *)
Definition sol_ok (D : list kdecl) (sol : solution) : Prop :=
  map fst sol = map kd_name D /\ forall k qs, assoc k sol = Some qs -> Forall (fun q => kfree q = true) qs.

Definition agree_kfree {C} (o1 o2 : obligation -> verdict C) : Prop :=
  forall ob, ob_kfree ob = true -> o1 ob = o2 ob.

Lemma kfind_In : forall D k, In k (map kd_name D) -> exists d, kfind D k = Some d.
Proof.
  intros D k. induction D as [|d D IH]; cbn; [contradiction | ].
  destruct (String.eqb (kd_name d) k) eqn:E; [eauto | ].
  intros [<- | H]; [rewrite String.eqb_refl in E; discriminate E | exact (IH H)].
Qed.

Lemma assoc_In : forall {A} k (l : list (string * A)), In k (map fst l) -> exists v, assoc k l = Some v.
Proof.
  intros A k l. induction l as [|[k' v'] l IH]; cbn; [contradiction | ].
  destruct (String.eqb k k') eqn:E; [eauto | ].
  intros [<- | H]; [rewrite String.eqb_refl in E; discriminate E | exact (IH H)].
Qed.

Lemma kfree_fand : forall p q, kfree p = true -> kfree q = true -> kfree (fand p q) = true.
Proof. intros p q Hp Hq. unfold fand. destruct (is_ftrue p), (is_ftrue q); cbn; rewrite ?Hp, ?Hq; reflexivity. Qed.

Lemma kfree_fconj : forall ps, Forall (fun p => kfree p = true) ps -> kfree (fconj ps) = true.
Proof.
  intros ps H. induction H as [|p ps Hp _ IH]; [reflexivity | ].
  unfold fconj. cbn [fold_right]. apply kfree_fand; assumption.
Qed.

Lemma apply_sol_kfree : forall D sol p, sol_ok D sol ->
  (forall k, In k (fkappas p) -> In k (map kd_name D)) -> kfree (apply_sol D sol p) = true.
Proof.
  intros D sol p [Hdom Hq].
  induction p as [| | | | k us | p IHp q IHq | p IHp q IHq | p IHp]; intros Hk; try reflexivity.
  - cbn [apply_sol].
    destruct (kfind_In D k (Hk k (or_introl eq_refl))) as [d Ed]. rewrite Ed.
    assert (Hin : In k (map fst sol)) by (rewrite Hdom; apply Hk; left; reflexivity).
    destruct (assoc_In k sol Hin) as [qs Eq]. rewrite Eq.
    apply kfree_fconj, Forall_map. eapply Forall_impl; [ | exact (Hq k qs Eq)].
    intros q' Hq'. unfold kinst. rewrite kfree_subst. exact Hq'.
  - cbn [apply_sol]. apply kfree_fand; [apply IHp | apply IHq]; intros k Hin; apply Hk; cbn; apply in_or_app; auto.
  - cbn [apply_sol kfree]. rewrite IHp, IHq; [reflexivity | ..]; intros k Hin; apply Hk; cbn; apply in_or_app; auto.
  - cbn [apply_sol kfree]. exact (IHp Hk).
Qed.

Lemma hyps_kfree : forall D sol h, sol_ok D sol -> horn_ok D h ->
  forallb kfree (map (apply_sol D sol) (h_hyps h)) = true.
Proof.
  intros D sol h Hs (_ & _ & Hk). apply forallb_forall. intros p Hp.
  apply in_map_iff in Hp as (p' & <- & Hp'). apply (apply_sol_kfree D sol p' Hs).
  intros k Hin. apply (proj1 (Forall_forall _ _) Hk). cbn. apply in_or_app. right.
  apply in_flat_map. eauto.
Qed.

Lemma update_dom : forall k qs sol, map fst (update k qs sol) = map fst sol.
Proof.
  intros k qs sol. induction sol as [|[k' qs'] sol IH]; [reflexivity | ].
  cbn. destruct (String.eqb k k'); cbn; [reflexivity | f_equal; exact IH].
Qed.

Lemma assoc_update : forall x k qs sol v,
  assoc x (update k qs sol) = Some v -> v = qs \/ assoc x sol = Some v.
Proof.
  intros x k qs sol v. induction sol as [|[k' qs'] sol IH]; cbn; [discriminate | ].
  destruct (String.eqb k k'); cbn; destruct (String.eqb x k'); auto.
  intros H. injection H as <-. auto.
Qed.

Lemma sol_ok_update : forall D sol k qs kept, sol_ok D sol -> assoc k sol = Some qs -> incl kept qs ->
  sol_ok D (update k kept sol).
Proof.
  intros D sol k qs kept [Hdom Hq] Ea Hi. split; [rewrite update_dom; exact Hdom | ].
  intros x v Ex. destruct (assoc_update x k kept sol v Ex) as [-> | E].
  - exact (incl_Forall Hi (Hq k qs Ea)).
  - exact (Hq x v E).
Qed.

Lemma initial_ok : forall D, quals_kfree D -> sol_ok D (initial D).
Proof.
  intros D HD. split; [unfold initial; rewrite map_map; reflexivity | ].
  induction HD as [|d D Hd _ IH]; intros k qs E; cbn in E; [discriminate E | ].
  destruct (String.eqb k (kd_name d)); [injection E as <-; exact Hd | exact (IH k qs E)].
Qed.

Section Agree.
  Context {C : Type} (o1 o2 : obligation -> verdict C) (D : list kdecl).
  Hypothesis Hagree : agree_kfree o1 o2.

  Lemma filter_quals_incl : forall (o : obligation -> verdict C) A l d us qs kept removed,
    filter_quals o A l d us qs = Ok (kept, removed) -> incl kept qs.
  Proof.
    intros o A l d us qs. induction qs as [|q qs IH]; intros kept removed H; cbn in H.
    - injection H as <- _. apply incl_nil_l.
    - destruct (o _); [ | | discriminate H]; bind_in H r Hr; injection H as <- _; destruct r as [k' r'];
        specialize (IH _ _ Hr); cbn; [apply incl_cons; [left; reflexivity | ] | ]; apply incl_tl; exact IH.
  Qed.

  Lemma filter_quals_agree : forall A l d us qs,
    forallb kfree A = true -> Forall (fun q => kfree q = true) qs ->
    filter_quals o1 A l d us qs = filter_quals o2 A l d us qs.
  Proof.
    intros A l d us qs HA Hqs. induction Hqs as [|q qs Hq _ IH]; [reflexivity | ].
    cbn. rewrite Hagree by (unfold ob_kfree; cbn; rewrite HA; unfold kinst; rewrite kfree_subst; exact Hq).
    rewrite IH. reflexivity.
  Qed.

  Lemma step_agree : forall sol h log, sol_ok D sol -> horn_ok D h -> step o1 D sol h log = step o2 D sol h log.
  Proof.
    intros sol h log Hs Hh. unfold step.
    destruct (h_goal h) as [k us | p]; [ | reflexivity].
    destruct (kfind D k) as [d | ]; [ | reflexivity].
    destruct (assoc k sol) as [qs | ] eqn:Ea; [ | reflexivity].
    rewrite (filter_quals_agree _ _ _ _ qs (hyps_kfree D sol h Hs Hh) (proj2 Hs k qs Ea)). reflexivity.
  Qed.

  Lemma step_sol_ok : forall (o : obligation -> verdict C) sol h log log' sol' b,
    sol_ok D sol -> step o D sol h log = (log', Ok (sol', b)) -> sol_ok D sol'.
  Proof.
    intros o sol h log log' sol' b Hs H. unfold step in H.
    destruct (h_goal h) as [k us | p]; [ | injection H as _ <- _; exact Hs].
    destruct (kfind D k) as [d | ]; [ | discriminate H].
    destruct (assoc k sol) as [qs | ] eqn:Ea; [ | discriminate H].
    destruct (filter_quals _ _ _ _ _ _) as [[kept removed] | e] eqn:Ef; [ | discriminate H].
    cbn in H. injection H as _ <- _.
    exact (sol_ok_update D sol k qs kept Hs Ea (filter_quals_incl _ _ _ _ _ _ _ _ Ef)).
  Qed.

  Lemma round_sol_ok : forall (o : obligation -> verdict C) hs sol changed log log' sol' b,
    sol_ok D sol -> round o D sol hs changed log = (log', Ok (sol', b)) -> sol_ok D sol'.
  Proof.
    intros o hs. induction hs as [|h hs IH]; intros sol changed log log' sol' b Hs H; cbn in H.
    - injection H as _ <- _. exact Hs.
    - apply tbind_ok in H as (log1 & [s1 b1] & Hstep & H).
      exact (IH _ _ _ _ _ _ (step_sol_ok o _ _ _ _ _ _ Hs Hstep) H).
  Qed.

  Lemma round_agree : forall hs sol changed log, sol_ok D sol -> Forall (horn_ok D) hs ->
    round o1 D sol hs changed log = round o2 D sol hs changed log.
  Proof.
    intros hs. induction hs as [|h hs IH]; intros sol changed log Hs Hhs; [reflexivity | ].
    inversion Hhs as [|? ? Hh Hhs']; subst. cbn. unfold tbind.
    rewrite (step_agree sol h log Hs Hh).
    destruct (step o2 D sol h log) as [log1 [[s1 b1] | e]] eqn:E; [ | reflexivity].
    exact (IH _ _ _ (step_sol_ok o2 _ _ _ _ _ _ Hs E) Hhs').
  Qed.

  Lemma iterate_sol_ok : forall (o : obligation -> verdict C) fuel n sol hs log log' sol',
    sol_ok D sol -> iterate o D fuel n sol hs log = (log', Ok sol') -> sol_ok D sol'.
  Proof.
    intros o fuel. induction fuel as [|f IH]; intros n sol hs log log' sol' Hs H; cbn in H; [discriminate H | ].
    unfold tbind at 1 in H. cbn in H. apply tbind_ok in H as (log1 & [s1 b1] & Hr & H).
    pose proof (round_sol_ok o _ _ _ _ _ _ _ Hs Hr) as Hs1. cbn in H.
    destruct b1; [exact (IH _ _ _ _ _ _ Hs1 H) | injection H as _ <-; exact Hs1].
  Qed.

  Lemma iterate_agree : forall fuel n sol hs log, sol_ok D sol -> Forall (horn_ok D) hs ->
    iterate o1 D fuel n sol hs log = iterate o2 D fuel n sol hs log.
  Proof.
    intros fuel. induction fuel as [|f IH]; intros n sol hs log Hs Hhs; [reflexivity | ].
    cbn. unfold tbind. cbn. rewrite (round_agree hs sol false _ Hs Hhs).
    destruct (round o2 D sol hs false _) as [log1 [[s1 b1] | e]] eqn:E; [ | reflexivity].
    destruct b1; [ | reflexivity].
    exact (IH _ _ _ _ (round_sol_ok o2 _ _ _ _ _ _ _ Hs E) Hhs).
  Qed.

  Lemma check_fixed_agree : forall sol hs log, sol_ok D sol -> Forall (horn_ok D) hs ->
    check_fixed o1 D sol hs log = check_fixed o2 D sol hs log.
  Proof.
    intros sol hs log Hs Hhs. unfold check_fixed. revert log.
    induction Hhs as [|h hs Hh _ IH]; intros log; [reflexivity | ].
    cbn. unfold tbind. destruct (h_goal h) as [k us | p] eqn:Eg; [exact (IH log) | ].
    rewrite Hagree.
    - destruct (o2 _); [exact (IH log) | reflexivity | reflexivity].
    - unfold ob_kfree, fixed_ob. cbn. rewrite (hyps_kfree D sol h Hs Hh).
      destruct Hh as (_ & Hp & _). rewrite Eg in Hp. exact Hp.
  Qed.
End Agree.

Theorem weaken_kfree_queries : forall C (o1 o2 : obligation -> verdict C) D hs,
  quals_kfree D -> Forall (horn_ok D) hs -> agree_kfree o1 o2 ->
  forall log, weaken o1 D hs log = weaken o2 D hs log.
Proof.
  intros C o1 o2 D hs HD Hhs Ha log. unfold weaken, tbind.
  rewrite (iterate_agree o1 o2 D Ha _ _ _ hs log (initial_ok D HD) Hhs).
  destruct (iterate o2 D _ _ _ hs log) as [log1 [sol | e]] eqn:E; [ | reflexivity].
  rewrite (check_fixed_agree o1 o2 D Ha sol hs log1 (iterate_sol_ok D o2 _ _ _ _ _ _ _ (initial_ok D HD) E) Hhs).
  reflexivity.
Qed.
