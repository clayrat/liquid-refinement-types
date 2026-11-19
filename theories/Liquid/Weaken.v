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
    happens ([weaken_fuel_enough]).  That the result is the strongest
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
