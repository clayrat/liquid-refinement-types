(** * Facts about the evaluator

    - [evalFuel_mono]: an answer other than [Timeout] survives any
      increase of fuel; in particular [Value] does
      ([evalFuel_value_mono]).
    - [eval_typed]: in a typed program and an environment of the
      declared types, a typed expression answers [Timeout], a [Value] of
      its type, or [Stuck] on [get] out of bounds: no failure of typing
      is reached;
    - an environment extended by a name fresh for [Γ] keeps the types of
      [Γ] ([env_ok_fresh]) and the values of the atoms typed in [Γ]
      ([eval_atoms_fresh]). *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Lang Require Import Syntax Eval Typing.

Local Open Scope Z_scope.

(** ** Lookup *)

Lemma lookup_In : forall {A} y (l : list (string * A)) a, lookup y l = Some a -> In (y, a) l.
Proof.
  intros A y l. induction l as [|[z b] l IH]; intros a H; cbn in H; [discriminate H | ].
  destruct (String.eqb_spec y z) as [-> | ]; [injection H as ->; now left | right; auto].
Qed.

Lemma lookup_cons_neq : forall {A} x y (a : A) l, y <> x -> lookup y ((x, a) :: l) = lookup y l.
Proof. intros A x y a l H. cbn. destruct (String.eqb_spec y x); [contradiction | reflexivity]. Qed.

Lemma lookup_none_not_in : forall {A} x (l : list (string * A)), lookup x l = None -> ~ In x (map fst l).
Proof.
  intros A x l. induction l as [|[y a] l IH]; cbn; [auto | ].
  destruct (String.eqb_spec x y); [discriminate | ]. intros H [<- | Hin]; [congruence | exact (IH H Hin)].
Qed.

(** ** Monotonicity in fuel *)

Lemma evalFuel_mono : forall k k' P ρ e a,
  (k <= k')%nat -> evalFuel k P ρ e = a -> a <> Timeout -> evalFuel k' P ρ e = a.
Proof.
  induction k as [|k IH]; intros k' P ρ e a Hle H Ha; cbn in H; [congruence | ].
  destruct k' as [|k']; [lia | ]. cbn.
  destruct e as [a0 | x p args e' | x f args e' | c e1 e2 | x e1 h t e2].
  - exact H.
  - destruct (eval_atoms ρ args); [ | exact H].
    destruct (eval_prim p l); [ | exact H]. apply IH; auto. lia.
  - destruct (find_fun f P) as [fd | ]; [ | exact H].
    destruct (eval_atoms ρ args) as [vs | ]; [ | exact H].
    destruct (bind_params (fd_params fd) vs) as [ρf | ]; [ | exact H].
    destruct (evalFuel k P ρf (fd_body fd)) as [v | | why] eqn:Eb.
    + rewrite (IH k' P ρf (fd_body fd) (Value v)); [ | lia | exact Eb | discriminate].
      apply IH; auto. lia.
    + congruence.
    + rewrite (IH k' P ρf (fd_body fd) (Stuck why)); [exact H | lia | exact Eb | discriminate].
  - destruct (eval_cond ρ c) as [[|] | ]; [ | | exact H]; apply IH; auto; lia.
  - destruct (lookup x ρ) as [[| | | | [|z l]] | ]; try exact H; apply IH; auto; lia.
Qed.

Corollary evalFuel_value_mono : forall k k' P ρ e v,
  (k <= k')%nat -> evalFuel k P ρ e = Value v -> evalFuel k' P ρ e = Value v.
Proof. intros. eapply evalFuel_mono; eauto. discriminate. Qed.

(** ** No failure of typing *)

Definition has_ty (v : value) (T : ty) : Prop :=
  match v, T with
  | VInt _, TyInt | VBool _, TyBool | VUnit, TyUnit | VArr _, TyArr | VList _, TyList => True
  | _, _ => False
  end.

Definition env_ok (ρ : env) (Γ : tenv) : Prop :=
  forall x T, lookup x Γ = Some T -> exists v, lookup x ρ = Some v /\ has_ty v T.

Definition typed_answer (a : answer) (T : ty) : Prop :=
  a = Timeout \/ (exists v, a = Value v /\ has_ty v T) \/ (exists l i n, a = Stuck (SBounds l i n)).

Lemma env_ok_cons : forall ρ Γ x v T, env_ok ρ Γ -> has_ty v T -> env_ok ((x, v) :: ρ) ((x, T) :: Γ).
Proof.
  intros ρ Γ x v T H Hv y U Hy. cbn in *.
  destruct (String.eqb y x); [injection Hy as <-; eauto | auto].
Qed.

Lemma env_ok_fresh : forall Γ ρ x v, lookup x Γ = None -> env_ok ρ Γ -> env_ok ((x, v) :: ρ) Γ.
Proof.
  intros Γ ρ x v Hx H y T Hy. rewrite lookup_cons_neq; [exact (H y T Hy) | ].
  intros ->. rewrite Hx in Hy. discriminate.
Qed.

Lemma eval_atom_typed : forall ρ Γ a T, env_ok ρ Γ -> atom_ty Γ a = Some T ->
  exists v, eval_atom ρ a = Some v /\ has_ty v T.
Proof.
  intros ρ Γ a T H Ha. destruct a; cbn in *; try (injection Ha as <-; eexists; split; reflexivity).
  exact (H x T Ha).
Qed.

Lemma eval_atoms_typed : forall ρ Γ args Ts, env_ok ρ Γ -> atoms_ty Γ args = Some Ts ->
  exists vs, eval_atoms ρ args = Some vs /\ Forall2 has_ty vs Ts.
Proof.
  intros ρ Γ args. induction args as [|a args IH]; intros Ts H Ha; cbn in *.
  - injection Ha as <-. exists []. split; [reflexivity | constructor].
  - destruct (atom_ty Γ a) as [T | ] eqn:Ea; [ | discriminate Ha].
    destruct (atoms_ty Γ args) as [Ts' | ] eqn:Eas; [ | discriminate Ha].
    injection Ha as <-.
    destruct (eval_atom_typed ρ Γ a T H Ea) as (v & -> & Hv).
    destruct (IH Ts' H eq_refl) as (vs & -> & Hvs).
    exists (v :: vs). split; [reflexivity | constructor; auto].
Qed.

Lemma eval_atoms_fresh : forall Γ ρ x v args Ts,
  lookup x Γ = None -> atoms_ty Γ args = Some Ts -> eval_atoms ((x, v) :: ρ) args = eval_atoms ρ args.
Proof.
  intros Γ ρ x v args. induction args as [|a args IH]; intros Ts Hx Ha; cbn in *; [reflexivity | ].
  destruct (atom_ty Γ a) as [T | ] eqn:Ea; [ | discriminate].
  destruct (atoms_ty Γ args) as [Ts' | ]; [ | discriminate].
  rewrite (IH Ts' Hx eq_refl).
  assert (E : eval_atom ((x, v) :: ρ) a = eval_atom ρ a).
  { destruct a; cbn in Ea |- *; try reflexivity. apply lookup_cons_neq. intros ->. congruence. }
  now rewrite E.
Qed.

Lemma bind_params_typed : forall ps vs, Forall2 has_ty vs (map snd ps) ->
  exists ρ, bind_params ps vs = Some ρ /\ env_ok ρ ps.
Proof.
  intros ps. induction ps as [|[x T] ps IH]; intros vs H; cbn in *.
  - inversion H; subst. exists []. split; [reflexivity | ]. intros y U Hy. discriminate Hy.
  - inversion H as [|v T' vs' Ts Hv Hvs]; subst.
    destruct (IH vs' Hvs) as (ρ & -> & Hρ).
    exists ((x, v) :: ρ). split; [reflexivity | ]. apply env_ok_cons; auto.
Qed.

Lemma bind_params_env_ok : forall ps vs ρf, bind_params ps vs = Some ρf -> Forall2 has_ty vs (map snd ps) -> env_ok ρf ps.
Proof.
  intros ps vs ρf Hb Hvs. destruct (bind_params_typed ps vs Hvs) as (ρ' & E & H).
  rewrite Hb in E. injection E as <-. exact H.
Qed.

Lemma eval_prim_typed : forall p vs, Forall2 has_ty vs (fst (prim_sig p)) ->
  (exists v, eval_prim p vs = Ok v /\ has_ty v (snd (prim_sig p))) \/
  (exists l i n, eval_prim p vs = Err (SBounds l i n)).
Proof.
  intros p vs H. destruct p; cbn in H;
    repeat match goal with
           | H : Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
           | H : Forall2 _ _ [] |- _ => inversion H; subst; clear H
           end;
    repeat match goal with
           | v : value |- _ => destruct v; cbn in *; try contradiction
           end; cbn.
  all: try (left; eexists; split; [reflexivity | exact I]).
  unfold get_at. destruct (_ && _); [left; eexists; split; [reflexivity | exact I] | right; eauto].
Qed.

Lemma eval_cond_typed : forall ρ Γ c, env_ok ρ Γ -> cond_ok Γ c = true -> exists b, eval_cond ρ c = Some b.
Proof.
  intros ρ Γ c H Hc. destruct c as [a | c a1 a2]; cbn in Hc; apply args_ok_atoms_ty in Hc; cbn in Hc.
  - destruct (atom_ty Γ a) as [T | ] eqn:Ea; [ | discriminate Hc]. injection Hc as ->.
    destruct (eval_atom_typed ρ Γ a TyBool H Ea) as ([] & E & Hv); try contradiction.
    cbn. rewrite E. eauto.
  - destruct (atom_ty Γ a1) as [T1 | ] eqn:E1; [ | discriminate Hc].
    destruct (atom_ty Γ a2) as [T2 | ] eqn:E2; [ | discriminate Hc].
    injection Hc as -> ->.
    destruct (eval_atom_typed ρ Γ a1 TyInt H E1) as ([] & F1 & Hv1); try contradiction.
    destruct (eval_atom_typed ρ Γ a2 TyInt H E2) as ([] & F2 & Hv2); try contradiction.
    cbn. rewrite F1, F2. eauto.
Qed.

Lemma typed_answer_bounds : forall l i n T, typed_answer (Stuck (SBounds l i n)) T.
Proof. intros. right; right; eauto. Qed.

Theorem eval_typed : forall k P ρ Γ e T,
  ty_prog P = Ok tt -> env_ok ρ Γ -> ty_expr P Γ e = Ok T -> typed_answer (evalFuel k P ρ e) T.
Proof.
  induction k as [|k IH]; intros P ρ Γ e T HP Hρ He; [left; reflexivity | ].
  destruct e as [a | x p args e' | x f args e' | c e1 e2 | x e1 h t e2]; cbn in He |- *.
  - destruct (atom_ty Γ a) as [T' | ] eqn:Ea; [ | discriminate He]. injection He as <-.
    destruct (eval_atom_typed ρ Γ a T' Hρ Ea) as (v & -> & Hv). right; left; eauto.
  - bind_in He u1 H1. bind_in He u2 H2.
    apply require_ok, args_ok_atoms_ty in H1.
    destruct (eval_atoms_typed ρ Γ args _ Hρ H1) as (vs & -> & Hvs).
    destruct (eval_prim_typed p vs Hvs) as [(v & -> & Hv) | (l & i & n & ->)].
    + eapply IH; [exact HP | apply env_ok_cons; eauto | exact He].
    + apply typed_answer_bounds.
  - destruct (find_fun f P) as [fd | ] eqn:Ef; [ | discriminate He].
    bind_in He u1 H1. bind_in He u2 H2.
    apply require_ok, args_ok_atoms_ty in H1.
    destruct (eval_atoms_typed ρ Γ args _ Hρ H1) as (vs & -> & Hvs).
    destruct (bind_params_typed (fd_params fd) vs Hvs) as (ρf & -> & Hρf).
    pose proof (ty_prog_fun P fd HP (find_fun_in _ _ _ Ef)) as Hfd. unfold ty_fun in Hfd.
    bind_in Hfd w1 Hw1. bind_in Hfd w2 Hw2. bind_in Hfd Tb Hb.
    apply require_ok, ty_eqb_eq in Hfd. subst Tb.
    destruct (IH P ρf (fd_params fd) (fd_body fd) (fd_ret fd) HP Hρf Hb)
      as [-> | [(v & -> & Hv) | (l & i & n & ->)]].
    + left; reflexivity.
    + eapply IH; [exact HP | apply env_ok_cons; eauto | exact He].
    + apply typed_answer_bounds.
  - bind_in He u1 H1. bind_in He T1 HT1. bind_in He T2 HT2. bind_in He u2 H2.
    injection He as <-.
    destruct (eval_cond_typed ρ Γ c Hρ (require_ok _ _ _ H1)) as (b & ->).
    apply require_ok, ty_eqb_eq in H2. subst T2.
    destruct b; eapply IH; eauto.
  - bind_in He u1 H1. bind_in He u2 H2. bind_in He u3 H3. bind_in He T1 HT1. bind_in He T2 HT2.
    bind_in He u4 H4. injection He as <-.
    apply require_ok in H1. destruct (lookup x Γ) as [[] | ] eqn:Ex; try discriminate H1.
    destruct (Hρ x TyList Ex) as (v & Ev & Hv). rewrite Ev.
    destruct v as [| | | | l]; try contradiction.
    apply require_ok, ty_eqb_eq in H4. subst T2.
    destruct l as [|z l].
    + eapply IH; eauto.
    + eapply IH; [exact HP | | exact HT2].
      apply env_ok_cons; [apply env_ok_cons; [exact Hρ | exact I] | exact I].
Qed.
