(** * A divergent function with the refinement [false]

      let rec loop x : {ν:Int | false} = loop x
      client = let r = loop 0 in get a 100

    The body is checked: the contract of the recursive call gives the
    hypothesis [false], which implies the required [false].  The client
    is accepted too, since the read stands under a false hypothesis.
    The operational guarantee is not broken: [evalFuel] answers
    [Timeout] for every fuel, and the read is never reached. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Check.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition loop_contract : contract := mkContract [ftrue] ffalse.

Definition loop_spec : spec := [("loop", loop_contract)].

Definition loop_def : fundef := mkFun "loop" [("x", TyInt)] TyInt (lcall "r" "loop" [AVar "x"] (ERet "r")).

Definition loop_prog : prog := [loop_def].

Definition client_loop : client :=
  mkClient [("a", TyArr)] [] (lcall "r" "loop" [num 0] (lget "y" "a" (num 100) (ERet "y"))) ftrue.

(** ** Divergence, directly

    [loop] times out for every fuel and every argument, and so does the
    client in every environment.  [loop] has no measure: at its call the
    argument is the parameter itself, so the obligation of decrease is
    [μ < μ], which no sound oracle proves ([loop_no_measure]).  The
    contracts accept [loop]; the check of termination does not. *)

From Stdlib Require Import Lia.
From Liquid.Logic Require Import Subst Obligation.
From Liquid.Refine Require Import Measure.

Definition loop_measures : measures := [("loop", TVar "x")].

Lemma loop_body_timeout : forall k v, evalFuel k loop_prog [("x", v)] (fd_body loop_def) = Timeout.
Proof.
  induction k as [|k IH]; intros v; [reflexivity | ].
  cbn. cbn in IH. rewrite IH. reflexivity.
Qed.

Theorem loop_diverges : forall k v, run_fun k loop_prog "loop" [v] = Timeout.
Proof. intros k v. exact (loop_body_timeout k v). Qed.

Theorem client_loop_diverges : forall ρ, diverges loop_prog ρ (cl_expr client_loop).
Proof.
  intros ρ [|k]; [reflexivity | ].
  pose proof (loop_body_timeout k (VInt 0)) as H. cbn in H |- *. rewrite H. reflexivity.
Qed.

Lemma tsubst_self : forall x t, tsubst (inst_subst [(x, TyInt)] [AVar x]) t = t.
Proof.
  intros x t. induction t as [y | z | t1 IH1 t2 IH2 | t1 IH1 t2 IH2 | c t IH | a]; cbn in *; try congruence.
  destruct (String.eqb y x) eqn:E; [apply String.eqb_eq in E; subst; reflexivity | reflexivity].
Qed.

Theorem loop_no_measure : forall C (oracle : obligation -> verdict C) μ,
  oracle_sound oracle -> accepted (check_measures oracle loop_prog loop_spec [("loop", μ)]) = false.
Proof.
  intros C oracle μ Ho. destruct (accepted _) eqn:H; [exfalso | reflexivity].
  destruct (check_measures_complete oracle _ _ _ H) as (_ & _ & Hp).
  set (ob := mkOb (LMeasureDecr "loop" "r") [] (FLt (tsubst (inst_subst [("x", TyInt)] [AVar "x"]) μ) μ)).
  assert (Hin : In ob (measure_obligations loop_prog loop_spec [("loop", μ)])) by (cbn; auto).
  pose proof (oracle_proved oracle ob Ho (Hp ob Hin) no_kappa (mkVal (fun _ => 0) (fun _ => false) (fun _ => 0))) as V.
  unfold ob_holds, ob in V. rewrite tsubst_self in V. cbn in V.
  specialize (V (fun _ => Z.le_refl 0) (Forall_nil _)). lia.
Qed.
