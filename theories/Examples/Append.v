(** * The length of [append] (stage 8, demonstration 5)

      append : xs:List → ys:List → {ν:List | len ν = len xs + len ys}
      append xs ys =
        match xs with
        | nil → ys
        | cons h t → let r = append t ys in let z = cons h r in z

    The equations of the measure [len] come as contracts: the branches of
    [match] get [len xs = 0] and [len xs = 1 + len t], [cons h r] returns
    [len ν = 1 + len r]; the contract of the recursive call gives the
    hypothesis of induction [len r = len t + len ys].  What is left is
    local arithmetic.  The branch [nil] is in the difference fragment as
    it is: [len ys = len xs + len ys] under [len xs = 0].  The branch
    [cons] is not — three lengths in one equality — and the solver
    eliminates [len xs], [len r] and [len z] (Solver/Elim.v); the goal
    becomes [0 = 0].  With the summands swapped in the contract,
    [len ν = len ys + len xs], nothing changes: the commutativity of [+]
    is the collection of like terms, with no transport by a proof as for
    [plus2] in the lectures 7–8.

    [append_valid] proves the same obligations in Rocq by [lia] on the
    semantics in [Prop]: a check by the kernel independent of the
    solver.  The measure [len xs] decreases at the recursive call
    ([append_measure_accepted]); [append_fuel] gives the exact fuel,
    [2·len xs + 2], and the value, [xs ++ ys].

    [client_ex1] is exercise 1 of the lecture,

      x:{x:Int | 0 ≤ x}, y:{y:Int | x < y} ⊢ let d = y − x in d : {ν:Int | 0 < ν},

    whose obligation [d = y − x ⊢ 0 < d] becomes the difference atom
    [0 < y − x] after the elimination of [d]. *)

From Stdlib Require Import String List ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula Obligation.
From Liquid.Lang Require Import Syntax Typing Eval EvalFacts.
From Liquid.Solver Require Import Prove.
From Liquid.Refine Require Import Spec Wp Gen Check Env Sound Measure.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition append_body : expr :=
  lmatch "xs" (ERet "ys") "h" "t"
    (lcall "r" "append" [AVar "t"; AVar "ys"] (lcons "z" "h" "r" (ERet "z"))).

Definition append_def : fundef := mkFun "append" [("xs", TyList); ("ys", TyList)] TyList append_body.

Definition append_prog : prog := [append_def].

Definition append_contract_with (len_sum : term) : contract :=
  mkContract [ftrue; ftrue] (FEq (TLen nu) len_sum).

Definition append_spec : spec := [("append", append_contract_with (TAdd (TLen "xs") (TLen "ys")))].
Definition append_spec_swapped : spec := [("append", append_contract_with (TAdd (TLen "ys") (TLen "xs")))].

(** A wrong contract: the length of the first list alone. *)
Definition append_spec_wrong : spec := [("append", append_contract_with (TLen "xs"))].

Definition append_measures : measures := [("append", TLen "xs")].

(** ** Accepted by the solver, in both orders *)

Lemma append_accepted : accepted (check_prog prove append_prog append_spec) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma append_swapped_accepted : accepted (check_prog prove append_prog append_spec_swapped) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma append_wrong_rejected : accepted (check_prog prove append_prog append_spec_wrong) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma append_measure_accepted : accepted (check_measures prove append_prog append_spec append_measures) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The same obligations by [lia] *)

Ltac lia_obligations H :=
  vm_compute in H;
  repeat match goal with
         | H : _ \/ _ |- _ => destruct H as [H | H]
         | H : False |- _ => destruct H
         end;
  subst; intros ki ρ Hl Hh; unfold ob_holds in *; cbn -[Z.add] in *;
  repeat match goal with
         | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
         | H : Forall _ [] |- _ => clear H
         end;
  cbn -[Z.add] in *; lia.

Theorem append_valid : forall ob, In ob (prog_obligations RuleName append_prog append_spec) -> valid ob.
Proof. intros ob H. lia_obligations H. Qed.

Theorem append_swapped_valid : forall ob,
  In ob (prog_obligations RuleName append_prog append_spec_swapped) -> valid ob.
Proof. intros ob H. lia_obligations H. Qed.

(** ** Runs *)

Definition append_env (xs ys : list Z) : env := [("xs", VList xs); ("ys", VList ys)].

(** Two nodes per element of [xs] and two at the end. *)
Theorem append_fuel : forall xs ys k, (2 * length xs + 2 <= k)%nat ->
  evalFuel k append_prog (append_env xs ys) append_body = Value (VList (xs ++ ys)).
Proof.
  induction xs as [|x xs IH]; intros ys k Hk.
  - do 2 (destruct k as [|k]; [cbn in Hk; lia | ]). reflexivity.
  - do 2 (destruct k as [|k]; [cbn in Hk; lia | ]).
    pose proof (IH ys k ltac:(cbn in Hk; lia)) as Hrec.
    cbn - [evalFuel]. cbn [evalFuel lookup String.eqb Ascii.eqb Bool.eqb eval_atoms eval_atom find_fun fd_name].
    change (evalFuel k append_prog [("xs", VList xs); ("ys", VList ys)] append_body = Value (VList (xs ++ ys)))
      in Hrec.
    cbn. rewrite Hrec.
    destruct k as [|[|k]]; [cbn in Hk; lia | cbn in Hk; lia | reflexivity].
Qed.

Theorem append_runs : forall xs ys, exists k,
  run_fun k append_prog "append" [VList xs; VList ys] = Value (VList (xs ++ ys)).
Proof. intros xs ys. exists (2 * length xs + 2)%nat. apply append_fuel. lia. Qed.

(** The guarantee of the first algorithm: never [Stuck], and the length. *)
Theorem append_length : forall xs ys k v,
  run_fun k append_prog "append" [VList xs; VList ys] = Value v ->
  exists l, v = VList l /\ length l = (length xs + length ys)%nat.
Proof.
  intros xs ys k v H.
  change (evalFuel k append_prog (append_env xs ys) append_body = Value v) in H.
  pose proof (check_prog_sound prove append_prog append_spec prove_sound append_accepted k append_def
                [VList xs; VList ys] (append_env xs ys) (or_introl eq_refl) eq_refl
                ltac:(repeat constructor) ltac:(repeat constructor)) as G.
  change (fd_body append_def) with append_body in G. rewrite H in G.
  pose proof (eval_typed k append_prog (append_env xs ys) [("xs", TyList); ("ys", TyList)] append_body TyList
                eq_refl (bind_params_env_ok [("xs", TyList); ("ys", TyList)] [VList xs; VList ys] (append_env xs ys)
                           eq_refl ltac:(repeat constructor)) eq_refl) as T.
  rewrite H in T. destruct T as [E | [(w & E & Hw) | (l & i & n & E)]]; try discriminate E.
  injection E as ->. destruct w as [| | | | l]; try contradiction.
  exists l. split; [reflexivity | ].
  unfold answer_ok, hold in G. cbn -[Z.add] in G. lia.
Qed.

(** ** Exercise 1 *)

Definition client_ex1 : client :=
  mkClient [("x", TyInt); ("y", TyInt)] [FLe (TConst 0) (TVar "x"); FLt (TVar "x") (TVar "y")]
           (lsub "d" "y" "x" (ERet "d")) (FLt (TConst 0) (TVar nu)).

Lemma client_ex1_accepted : accepted (check_client prove [] [] client_ex1) = true.
Proof. vm_compute. reflexivity. Qed.
