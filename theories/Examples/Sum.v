(** * The traversal of an array

      let rec go a n i =
        if i < n then
          let x = get a i in
          let j = i + 1 in
          let s = go a n j in
          x + s
        else 0

      let sum a =
        let n = length a in
        go a n 0

    [go] gets the array and its length as parameters, so the refinement
    of [i] may mention [n].  The fixed part of the contract of [go]
    repeats the facts about the length: [n:{n:Int | n = len a ∧ 0 ≤ n}].
    The refinement of [i] is given here, [0 ≤ i ∧ i ≤ n]; Liquid/ finds
    it again.  The results are plain [Int]: only the safety of the
    reads is checked.

    [sum] is listed before [go]: the order of the definitions does not
    matter to the checker, and it is the order in which weakening meets
    the initial call and the recursive one.

    [go_le] is the error of bounds: the condition [i ≤ n] instead of
    [i < n]. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Check.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition len_refinement : formula := FAnd (FEq (TVar "n") (TLen "a")) (FLe (TConst 0) (TVar "n")).
Definition i_invariant : formula := FAnd (FLe (TConst 0) (TVar "i")) (FLe (TVar "i") (TVar "n")).

Definition go_contract (inv : formula) : contract := mkContract [ftrue; len_refinement; inv] ftrue.
Definition sum_contract : contract := mkContract [ftrue] ftrue.

Definition sum_spec_with (inv : formula) : spec := [("sum", sum_contract); ("go", go_contract inv)].
Definition sum_spec : spec := sum_spec_with i_invariant.

Definition go_body (c : cmp) : expr :=
  ifc c "i" "n"
    (lget "x" "a" "i" (ladd "j" "i" (num 1) (lcall "s" "go" [AVar "a"; AVar "n"; AVar "j"] (ladd "r" "x" "s" (ERet "r")))))
    (ERet (num 0)).

Definition go_params : list (string * ty) := [("a", TyArr); ("n", TyInt); ("i", TyInt)].

Definition go_def (c : cmp) : fundef := mkFun "go" go_params TyInt (go_body c).

Definition sum_def : fundef :=
  mkFun "sum" [("a", TyArr)] TyInt (llength "n" "a" (lcall "s" "go" [AVar "a"; AVar "n"; num 0] (ERet "s"))).

Definition sum_prog : prog := [sum_def; go_def CLt].
Definition sum_prog_le : prog := [sum_def; go_def CLe].

Definition arr (l : list Z) : value := VArr l.

(** ** The invariant as an unknown

    The refinement of [i] is replaced by [κ(i, n)] with the qualifiers

      Qκ = {0 ≤ i, i ≤ n, i < n, i = 0};

    the fixed part of the contract of [go], its result and [sum] stay.
    [quals_no_lower] drops [0 ≤ i]: the abstraction is then too coarse. *)

From Liquid.Liquid Require Import Template.

Definition kappa_name : string := "κ".

Definition quals : list formula :=
  [FLe (TConst 0) (TVar "i"); FLe (TVar "i") (TVar "n"); FLt (TVar "i") (TVar "n"); FEq (TVar "i") (TConst 0)].

Definition quals_no_lower : list formula := tl quals.

Definition go_template (qs : list formula) : ctemplate :=
  mkCT [fixed ftrue; fixed len_refinement; holed ftrue (mkHole kappa_name qs)] (fixed ftrue).

Definition sum_tspec (qs : list formula) : tspec := [("sum", of_contract sum_contract); ("go", go_template qs)].

(** A client of [go], checked separately: the call at [i = n].  It is
    the first constraint weakening meets, and removes [i < n] and
    [i = 0] before the definitions do; [0 ≤ i ∧ i ≤ n] is inferred all
    the same. *)
Definition client_go_n : client :=
  mkClient [("a", TyArr); ("n", TyInt)] [FEq (TVar "n") (TLen "a"); FLe (TConst 0) (TVar "n")]
           (lcall "r" "go" [AVar "a"; AVar "n"; AVar "n"] (ERet "r")) ftrue.

(** A qualifier outside the difference fragment: [0 ≤ i + n] holds
    under the invariant, but a sum of two variables is not a difference.
    At the recursive call weakening asks [0 ≤ j + n]; the solver answers
    [Unknown], also after eliminating [j = i + 1], and the inference
    answers [Undecided] rather than remove a qualifier that may be true.
    In a contract checked by the first algorithm the same refinement
    leaves an obligation [Unknown], and the program is not accepted. *)
Definition sum_qual : formula := FLe (TConst 0) (TAdd (TVar "i") (TVar "n")).

Definition quals_outside : list formula := quals ++ [sum_qual].

Definition sum_spec_outside : spec := sum_spec_with (FAnd i_invariant sum_qual).

(** ** Termination

    The measure of [go] is the number of elements left, [n − i]: it is
    non-negative under the invariant and decreases at the recursive
    call, where [j = i + 1].  Its two obligations are checked by
    [check_measures]; the non-negativity needs [i ≤ n], which the
    safety of the reads does not: with the invariant [0 ≤ i] alone the
    contracts are accepted and the measure is not.

    Independently of the measures, [sum_fuel] proves the termination of
    [sum] directly, with the fuel it needs, [4·len a + 4], and the value
    it returns.  [sum_never_stuck] is the guarantee of the first
    algorithm (Refine/Sound.v) applied to the accepted contracts. *)

From Stdlib Require Import Lia.
From Liquid.Lang Require Import EvalFacts.
From Liquid.Logic Require Import Obligation.
From Liquid.Solver Require Import Prove.
From Liquid.Refine Require Import Sound Measure.

Definition go_measure : term := TSub (TVar "n") (TVar "i").
Definition sum_measures : measures := [("go", go_measure)].

Definition i_lower : formula := FLe (TConst 0) (TVar "i").
Definition sum_spec_lower : spec := sum_spec_with i_lower.

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

(** The environment of the body of [go] at the index [i]. *)
Definition go_env (l : list Z) (i : Z) : env := [("a", VArr l); ("n", VInt (Z.of_nat (length l))); ("i", VInt i)].

Lemma zsum_skipn : forall l m, (m < length l)%nat -> zsum (skipn m l) = nth m l 0 + zsum (skipn (S m) l).
Proof.
  induction l as [|x l IH]; intros [|m] H; cbn [skipn nth length] in H |- *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

(** With [m] elements left, [go] needs the fuel [4·m + 2]: four nodes
    per element and two at the end. *)
Lemma go_fuel : forall m l i k, 0 <= i -> i + Z.of_nat m = Z.of_nat (length l) -> (4 * m + 2 <= k)%nat ->
  evalFuel k sum_prog (go_env l i) (go_body CLt) = Value (VInt (zsum (skipn (Z.to_nat i) l))).
Proof.
  induction m as [|m IH]; intros l i k Hi Hm Hk.
  - do 2 (destruct k as [|k]; [lia | ]).
    assert (E : (i <? Z.of_nat (length l)) = false) by (apply Z.ltb_ge; lia).
    cbn. rewrite E.
    rewrite skipn_all2 by lia. reflexivity.
  - do 4 (destruct k as [|k]; [lia | ]).
    assert (E : (i <? Z.of_nat (length l)) = true) by (apply Z.ltb_lt; lia).
    assert (G : ((0 <=? i) && (i <? Z.of_nat (length l)))%bool = true)
      by (rewrite E; apply Z.leb_le in Hi; rewrite Hi; reflexivity).
    pose proof (IH l (i + 1) k ltac:(lia) ltac:(lia) ltac:(lia)) as Hrec.
    cbn in Hrec |- *. rewrite E. unfold get_at. rewrite G.
    change [("a", VArr l); ("n", VInt (Z.of_nat (length l))); ("i", VInt (i + 1))] with (go_env l (i + 1)).
    rewrite Hrec.
    destruct k as [|[|k]]; [lia | lia | ]. cbn.
    rewrite (zsum_skipn l (Z.to_nat i)) by lia.
    rewrite Z2Nat.inj_add, Nat.add_1_r by lia. reflexivity.
Qed.

Theorem sum_fuel : forall l k, (4 * length l + 4 <= k)%nat ->
  run_fun k sum_prog "sum" [VArr l] = Value (VInt (zsum l)).
Proof.
  intros l k Hk. do 2 (destruct k as [|k]; [lia | ]).
  pose proof (go_fuel (length l) l 0 k ltac:(lia) ltac:(lia) ltac:(lia)) as Hgo.
  cbn in Hgo |- *.
  change [("a", VArr l); ("n", VInt (Z.of_nat (length l))); ("i", VInt 0)] with (go_env l 0).
  rewrite Hgo. destruct k as [|k]; [lia | ]. reflexivity.
Qed.

(** For every array there is a fuel at which [sum] returns a value. *)
Theorem sum_terminates : forall l, exists k, run_fun k sum_prog "sum" [VArr l] = Value (VInt (zsum l)).
Proof. intros l. exists (4 * length l + 4)%nat. apply sum_fuel. lia. Qed.

Lemma sum_accepted : accepted (check_prog prove sum_prog sum_spec) = true.
Proof. vm_compute. reflexivity. Qed.

(** For every array and every fuel, no read is out of bounds. *)
Theorem sum_never_stuck : forall l k why, run_fun k sum_prog "sum" [VArr l] <> Stuck why.
Proof.
  intros l k why H.
  pose proof (check_prog_sound prove sum_prog sum_spec prove_sound sum_accepted k sum_def [VArr l] [("a", VArr l)]) as G.
  change (evalFuel k sum_prog [("a", VArr l)] (fd_body sum_def) = Stuck why) in H. rewrite H in G.
  apply G; [left; reflexivity | reflexivity | repeat constructor | repeat constructor].
Qed.
