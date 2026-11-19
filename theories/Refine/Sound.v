(** * The operational guarantee of the first algorithm

    If the program is typed, its contracts well-scoped, and every
    obligation of [check_prog] is valid — in particular, if
    [check_prog] accepted it with a sound oracle — then for every fuel
    [k] the run of a function whose arguments satisfy its precondition
    answers [Timeout] or [Value v] with the postcondition of [v]; [Stuck]
    is excluded ([check_prog_sound]).  The same holds for a client
    accepted by [check_client], in every environment of its types that
    satisfies [φ] ([check_client_sound]).

    The proof is one induction on fuel for expressions and calls
    together: a call with fuel [k+1] runs the body with fuel [k], and the
    induction hypothesis gives the contract of the callee at that fuel.
    Termination is assumed nowhere; [loop] with the postcondition
    [false] passes the same theorem.

    The link between programs and the logic is the valuation of an
    environment [val_of_env]: an integer variable is its value, a boolean
    one its value, an array name the length of its array.  Its pieces:

    - [holds_lookup_agree]: a formula depends only on the bindings of its
      names; with the freshness of the names bound by [let] and the scopes
      of the formulas, the hypotheses stay true when the environment is
      extended;
    - [inst_pre] and [inst_post]: the substitution of the formal
      parameters by the actual atoms is evaluating under the environment
      of the callee, and [ν] by the name of the result is binding [ν] to
      the returned value;
    - [prim_spec_sound]: the contracts of the primitives agree with their
      semantics: on typed arguments the precondition excludes [Stuck], and
      the result satisfies the postcondition. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing EvalFacts.
From Liquid.Refine Require Import Spec Wp Gen Check.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ** The valuation of an environment *)

Definition val_of_env (ρ : env) : valuation :=
  mkVal (fun x => match lookup x ρ with Some (VInt z) => z | _ => 0 end)
        (fun b => match lookup b ρ with Some (VBool c) => c | _ => false end)
        (fun a => match lookup a ρ with Some (VArr l) => Z.of_nat (List.length l) | _ => 0 end).

Lemma val_of_env_lens : forall ρ, lens_nonneg (val_of_env ρ).
Proof. intros ρ a. cbn. destruct (lookup a ρ) as [[]|]; lia. Qed.

Definition hold (ρ : env) (p : formula) : Prop := holds no_kappa (val_of_env ρ) p.

Definition answer_ok (a : answer) (ρ : env) (ψ : formula) : Prop :=
  match a with
  | Timeout => True
  | Value v => hold ((nu, v) :: ρ) ψ
  | Stuck _ => False
  end.

(** ** Names of formulas *)

Definition fnames (p : formula) : list string := fvars p ++ fbvars p ++ flens p.

Lemma holds_lookup_agree : forall ρ1 ρ2 p,
  (forall y, In y (fnames p) -> lookup y ρ1 = lookup y ρ2) -> hold ρ1 p <-> hold ρ2 p.
Proof.
  intros ρ1 ρ2 p H. unfold hold. apply holds_agree. unfold agree_on, fnames in *.
  split; [ | split]; intros y Hy; cbn; rewrite H; auto; apply in_or_app; [left | right; apply in_or_app; left
                                                                         | right; apply in_or_app; right]; exact Hy.
Qed.

Definition scoped (Γ : tenv) (p : formula) : Prop := formula_ok [] (scope_of Γ) p = true.

Lemma names_of_dom : forall T Γ y, In y (names_of T Γ) -> In y (map fst Γ).
Proof.
  intros T Γ y H. unfold names_of in H. apply in_map_iff in H as ([z U] & <- & Hin).
  apply filter_In in Hin as [Hin _]. apply in_map_iff. exists (z, U). auto.
Qed.

Lemma names_of_In : forall T Γ y, In y (names_of T Γ) -> exists U, In (y, U) Γ /\ U = T.
Proof.
  intros T Γ y H. unfold names_of in H. apply in_map_iff in H as ([z U] & <- & Hin).
  apply filter_In in Hin as [Hin HT]. cbn in HT. exists U. split; [exact Hin | exact (ty_eqb_eq _ _ HT)].
Qed.

Lemma scoped_names : forall Γ p, scoped Γ p -> forall y, In y (fnames p) -> In y (map fst Γ).
Proof.
  intros Γ p H y Hy. unfold scoped, formula_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hx Hb].
  rewrite subset_In in Hx, Hb, Hl. cbn in *.
  unfold fnames in Hy. apply in_app_or in Hy as [Hy | Hy]; [ | apply in_app_or in Hy as [Hy | Hy]];
    eapply names_of_dom; [apply Hx | apply Hb | apply Hl]; exact Hy.
Qed.

(** A larger context keeps a formula in scope. *)
Lemma scoped_mono : forall Γ Γ' p,
  (forall T y, In y (names_of T Γ) -> In y (names_of T Γ')) -> scoped Γ p -> scoped Γ' p.
Proof.
  intros Γ Γ' p Hsub H. unfold scoped, formula_ok in *.
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hx Hb].
  rewrite subset_In in Hx, Hb, Hl. cbn in *.
  rewrite Hk, andb_true_r.
  repeat (apply andb_true_intro; split); apply subset_In; intros y Hy; apply Hsub; auto.
Qed.

Lemma names_of_app : forall T Γ1 Γ2, names_of T (Γ1 ++ Γ2) = names_of T Γ1 ++ names_of T Γ2.
Proof. intros T Γ1 Γ2. unfold names_of. now rewrite filter_app, map_app. Qed.

Lemma names_of_cons : forall T x U Γ y, In y (names_of T Γ) -> In y (names_of T ((x, U) :: Γ)).
Proof.
  intros T x U Γ y H. unfold names_of in *. cbn. destruct (ty_eqb U T); [right | ]; exact H.
Qed.

Lemma scoped_cons : forall Γ x U p, scoped Γ p -> scoped ((x, U) :: Γ) p.
Proof. intros Γ x U p. apply scoped_mono. intros T y. apply names_of_cons. Qed.

Lemma scoped_cons_nu : forall Γ x U T p, scoped (Γ ++ [(nu, T)]) p -> scoped (((x, U) :: Γ) ++ [(nu, T)]) p.
Proof.
  intros Γ x U T p. apply scoped_mono. intros T' y. rewrite !names_of_app.
  intros H. apply in_app_or in H as [H | H]; apply in_or_app; [left; apply names_of_cons, H | right; exact H].
Qed.

(** ** Extending an environment by a fresh name *)

Lemma lookup_cons_neq : forall {A} x y (a : A) l, y <> x -> lookup y ((x, a) :: l) = lookup y l.
Proof. intros A x y a l H. cbn. destruct (String.eqb_spec y x); [contradiction | reflexivity]. Qed.

Lemma lookup_none_not_in : forall {A} x (Γ : list (string * A)), lookup x Γ = None -> ~ In x (map fst Γ).
Proof.
  intros A x Γ. induction Γ as [|[y a] Γ IH]; cbn; [auto | ].
  destruct (String.eqb_spec x y); [discriminate | ]. intros H [<- | Hin]; [congruence | exact (IH H Hin)].
Qed.

Lemma hold_fresh : forall Γ ρ x v p, lookup x Γ = None -> scoped Γ p -> hold ((x, v) :: ρ) p <-> hold ρ p.
Proof.
  intros Γ ρ x v p Hx Hp. apply holds_lookup_agree. intros y Hy.
  apply lookup_cons_neq. intros ->. apply (lookup_none_not_in _ _ Hx). exact (scoped_names Γ p Hp _ Hy).
Qed.

Lemma hold_fresh_nu : forall Γ ρ x v w T ψ,
  lookup x Γ = None -> x <> nu -> scoped (Γ ++ [(nu, T)]) ψ ->
  hold ((nu, w) :: (x, v) :: ρ) ψ <-> hold ((nu, w) :: ρ) ψ.
Proof.
  intros Γ ρ x v w T ψ Hx Hn Hp. apply holds_lookup_agree. intros y Hy. cbn.
  destruct (String.eqb_spec y nu); [reflexivity | ].
  pose proof (scoped_names _ _ Hp _ Hy) as Hin. rewrite map_app in Hin. apply in_app_or in Hin as [Hin | [Hin | []]];
    [ | cbn in Hin; congruence].
  destruct (String.eqb_spec y x); [subst; exfalso; exact (lookup_none_not_in _ _ Hx Hin) | reflexivity].
Qed.

(** ** Atoms and their values *)

Lemma atom_int : forall Γ ρ a, env_ok ρ Γ -> atom_ty Γ a = Some TyInt ->
  exists z, eval_atom ρ a = Some (VInt z) /\ teval (val_of_env ρ) (aterm a) = z.
Proof.
  intros Γ ρ a H Ha. destruct (eval_atom_typed ρ Γ a TyInt H Ha) as ([z| | |] & E & Hv); try contradiction.
  exists z. split; [exact E | ]. destruct a; cbn in E |- *; try discriminate E.
  - now rewrite E.
  - congruence.
Qed.

Lemma atom_bool : forall Γ ρ a, env_ok ρ Γ -> atom_ty Γ a = Some TyBool ->
  exists c, eval_atom ρ a = Some (VBool c) /\ beval (val_of_env ρ) (abatom a) = c.
Proof.
  intros Γ ρ a H Ha. destruct (eval_atom_typed ρ Γ a TyBool H Ha) as ([|c| |] & E & Hv); try contradiction.
  exists c. split; [exact E | ]. destruct a; cbn in E |- *; try discriminate E.
  - now rewrite E.
  - congruence.
Qed.

Lemma atom_arr : forall Γ ρ a, env_ok ρ Γ -> atom_ty Γ a = Some TyArr ->
  exists y l, a = AVar y /\ eval_atom ρ a = Some (VArr l) /\ lookup y ρ = Some (VArr l).
Proof.
  intros Γ ρ a H Ha. destruct (eval_atom_typed ρ Γ a TyArr H Ha) as ([| | |l] & E & Hv); try contradiction.
  destruct a; cbn in E, Ha; try discriminate. exists x, l. auto.
Qed.

Lemma atom_unit_free : forall Γ a T, atom_ty Γ a = Some T -> forall y, a = AVar y -> In y (map fst Γ).
Proof.
  intros Γ a T Ha y ->. cbn in Ha. induction Γ as [|[z U] Γ IH]; cbn in *; [discriminate | ].
  destruct (String.eqb_spec y z); [left; auto | right; auto].
Qed.

Lemma eval_atoms_fresh : forall Γ ρ x v args Ts,
  lookup x Γ = None -> atoms_ty Γ args = Some Ts -> eval_atoms ((x, v) :: ρ) args = eval_atoms ρ args.
Proof.
  intros Γ ρ x v args. induction args as [|a args IH]; intros Ts Hx Ha; cbn in *; [reflexivity | ].
  destruct (atom_ty Γ a) as [T | ] eqn:Ea; [ | discriminate].
  destruct (atoms_ty Γ args) as [Ts' | ]; [ | discriminate].
  rewrite (IH Ts' Hx eq_refl).
  assert (E : eval_atom ((x, v) :: ρ) a = eval_atom ρ a).
  { destruct a; cbn; try reflexivity.
    apply lookup_cons_neq. intros ->. exact (lookup_none_not_in _ _ Hx (atom_unit_free _ _ _ Ea _ eq_refl)). }
  now rewrite E.
Qed.

Lemma env_ok_fresh : forall Γ ρ x v, lookup x Γ = None -> env_ok ρ Γ -> env_ok ((x, v) :: ρ) Γ.
Proof.
  intros Γ ρ x v Hx H y T Hy. rewrite lookup_cons_neq; [exact (H y T Hy) | ].
  intros ->. rewrite Hx in Hy. discriminate.
Qed.

(** ** Substitution of the formals by the actual atoms *)

Lemma bind_atom_other : forall p T a σ ρ y, y <> p ->
  vint (subst_val (bind_atom p T a σ) ρ) y = vint (subst_val σ ρ) y /\
  vbool (subst_val (bind_atom p T a σ) ρ) y = vbool (subst_val σ ρ) y /\
  vlen (subst_val (bind_atom p T a σ) ρ) y = vlen (subst_val σ ρ) y.
Proof.
  intros p T a σ ρ y Hy. apply String.eqb_neq in Hy.
  destruct T, a; cbn; unfold arr_image; cbn; rewrite ?Hy; auto.
Qed.

Lemma agree_on_incl : forall xs bs ls xs' bs' ls' ρ1 ρ2, agree_on xs bs ls ρ1 ρ2 ->
  incl xs' xs -> incl bs' bs -> incl ls' ls -> agree_on xs' bs' ls' ρ1 ρ2.
Proof. intros xs bs ls xs' bs' ls' ρ1 ρ2 (A & B & C) H1 H2 H3. split; [ | split]; intros y Hy; auto. Qed.

Definition agree_ctx (Γ : tenv) (ρ1 ρ2 : valuation) : Prop :=
  agree_on (names_of TyInt Γ) (names_of TyBool Γ) (names_of TyArr Γ) ρ1 ρ2.

Lemma scoped_fv : forall Γ p, scoped Γ p ->
  incl (fvars p) (names_of TyInt Γ) /\ incl (fbvars p) (names_of TyBool Γ) /\ incl (flens p) (names_of TyArr Γ).
Proof.
  intros Γ p H. unfold scoped, formula_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hx Hb].
  rewrite subset_In in Hx, Hb, Hl. split; [ | split]; intros y Hy; auto.
Qed.

Lemma holds_agree_ctx : forall Γ ρ1 ρ2 p, scoped Γ p -> agree_ctx Γ ρ1 ρ2 ->
  holds no_kappa ρ1 p <-> holds no_kappa ρ2 p.
Proof.
  intros Γ ρ1 ρ2 p Hp H. apply holds_agree. destruct (scoped_fv Γ p Hp) as (A & B & C).
  exact (agree_on_incl _ _ _ _ _ _ _ _ H A B C).
Qed.

Lemma names_of_cons_inv : forall T p U Γ y, In y (names_of T ((p, U) :: Γ)) ->
  (y = p /\ U = T) \/ In y (names_of T Γ).
Proof.
  intros T p U Γ y H. unfold names_of in H. cbn in H.
  destruct (ty_eqb U T) eqn:E; cbn in H; [ | right; exact H].
  destruct H as [<- | H]; [left; split; [reflexivity | exact (ty_eqb_eq _ _ E)] | right; exact H].
Qed.

Lemma inst_agree : forall Γ ρ ps args vs ρf,
  NoDup (map fst ps) -> env_ok ρ Γ -> atoms_ty Γ args = Some (map snd ps) ->
  eval_atoms ρ args = Some vs -> bind_params ps vs = Some ρf ->
  agree_ctx ps (subst_val (inst_subst ps args) (val_of_env ρ)) (val_of_env ρf).
Proof.
  intros Γ ρ ps. induction ps as [|[p T] ps IH]; intros args vs ρf Hnd Hρ Ha He Hb.
  - split; [ | split]; intros y [].
  - destruct args as [|a args]; [discriminate Ha | ]. destruct vs as [|v vs]; cbn in Hb; [discriminate Hb | ].
    destruct (bind_params ps vs) as [ρf' | ] eqn:Eb; [ | discriminate Hb]. injection Hb as <-.
    cbn in Ha. destruct (atom_ty Γ a) as [U | ] eqn:Ea; [ | discriminate Ha].
    destruct (atoms_ty Γ args) as [Us | ] eqn:Eas; [ | discriminate Ha]. injection Ha as HU HUs. subst U.
    cbn in He. destruct (eval_atom ρ a) as [v' | ] eqn:Ev; [ | discriminate He].
    destruct (eval_atoms ρ args) as [vs' | ] eqn:Evs; [ | discriminate He]. injection He as <- <-.
    inversion Hnd as [|? ? Hp Hnd']; subst.
    destruct (IH args vs' ρf' Hnd' Hρ Eas Evs Eb) as (IHi & IHb & IHl).
    cbn [inst_subst].
    split; [ | split]; intros y Hy; apply names_of_cons_inv in Hy as [[-> ->] | Hy].
    + destruct (atom_int Γ ρ a Hρ Ea) as (z & Ez & Hz). rewrite Ev in Ez. injection Ez as ->.
      cbn. rewrite String.eqb_refl. cbn. exact Hz.
    + assert (y <> p) by (intros ->; apply Hp; eapply names_of_dom; exact Hy).
      destruct (bind_atom_other p T a (inst_subst ps args) (val_of_env ρ) y H) as (-> & _ & _).
      rewrite (IHi y Hy). cbn. now rewrite (proj2 (String.eqb_neq y p) H).
    + destruct (atom_bool Γ ρ a Hρ Ea) as (c & Ec & Hc). rewrite Ev in Ec. injection Ec as ->.
      cbn. rewrite String.eqb_refl. cbn. exact Hc.
    + assert (y <> p) by (intros ->; apply Hp; eapply names_of_dom; exact Hy).
      destruct (bind_atom_other p T a (inst_subst ps args) (val_of_env ρ) y H) as (_ & -> & _).
      rewrite (IHb y Hy). cbn. now rewrite (proj2 (String.eqb_neq y p) H).
    + destruct (atom_arr Γ ρ a Hρ Ea) as (w & l & -> & Ew & Hw). rewrite Ev in Ew. injection Ew as ->.
      cbn. unfold arr_image. cbn. rewrite ?String.eqb_refl, ?Hw. cbn. rewrite ?String.eqb_refl. reflexivity.
    + assert (y <> p) by (intros ->; apply Hp; eapply names_of_dom; exact Hy).
      destruct (bind_atom_other p T a (inst_subst ps args) (val_of_env ρ) y H) as (_ & _ & ->).
      rewrite (IHl y Hy). cbn. now rewrite (proj2 (String.eqb_neq y p) H).
Qed.

Lemma inst_pre : forall Γ ρ ps args vs ρf p,
  NoDup (map fst ps) -> env_ok ρ Γ -> atoms_ty Γ args = Some (map snd ps) ->
  eval_atoms ρ args = Some vs -> bind_params ps vs = Some ρf -> scoped ps p ->
  hold ρ (fsubst (inst_subst ps args) p) <-> hold ρf p.
Proof.
  intros Γ ρ ps args vs ρf p Hnd Hρ Ha He Hb Hp. unfold hold. rewrite holds_subst.
  exact (holds_agree_ctx ps _ _ p Hp (inst_agree Γ ρ ps args vs ρf Hnd Hρ Ha He Hb)).
Qed.

Lemma lookup_nu_cons : forall {A} (a : A) l, lookup nu ((nu, a) :: l) = Some a.
Proof. reflexivity. Qed.

Lemma inst_post : forall Γ ρ ps args vs ρf T x v p,
  NoDup (map fst ps) -> ~ In nu (map fst ps) -> env_ok ρ Γ -> atoms_ty Γ args = Some (map snd ps) ->
  eval_atoms ρ args = Some vs -> bind_params ps vs = Some ρf ->
  lookup x Γ = None -> x <> nu -> has_ty v T -> scoped (ps ++ [(nu, T)]) p ->
  hold ((x, v) :: ρ) (fsubst (res_subst T x (inst_subst ps args)) p) <-> hold ((nu, v) :: ρf) p.
Proof.
  intros Γ ρ ps args vs ρf T x v p Hnd Hnu Hρ Ha He Hb Hx Hxnu Hv Hp. unfold hold. rewrite holds_subst.
  apply (holds_agree_ctx (ps ++ [(nu, T)]) _ _ p Hp).
  pose proof (inst_agree Γ ((x, v) :: ρ) ps args vs ρf Hnd (env_ok_fresh Γ ρ x v Hx Hρ) Ha
                (eq_trans (eval_atoms_fresh Γ ρ x v args _ Hx Ha) He) Hb) as (Ai & Ab & Al).
  unfold agree_ctx. rewrite !names_of_app. unfold res_subst.
  assert (Hne : forall y T', In y (names_of T' ps) -> y <> nu)
    by (intros y T' Hy ->; apply Hnu; eapply names_of_dom; exact Hy).
  assert (Hx' : lookup x ((x, v) :: ρ) = Some v) by (cbn; now rewrite String.eqb_refl).
  split; [ | split]; intros y Hy; apply in_app_or in Hy as [Hy | Hy].
  - destruct (bind_atom_other nu T (AVar x) (inst_subst ps args) (val_of_env ((x, v) :: ρ)) y (Hne y _ Hy))
      as (-> & _ & _).
    rewrite (Ai y Hy). cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct v as [z| | |]; try contradiction. cbn. rewrite ?String.eqb_refl. cbn. now rewrite ?String.eqb_refl.
  - destruct (bind_atom_other nu T (AVar x) (inst_subst ps args) (val_of_env ((x, v) :: ρ)) y (Hne y _ Hy))
      as (_ & -> & _).
    rewrite (Ab y Hy). cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct v as [|c| |]; try contradiction. cbn. rewrite ?String.eqb_refl. cbn. now rewrite ?String.eqb_refl.
  - destruct (bind_atom_other nu T (AVar x) (inst_subst ps args) (val_of_env ((x, v) :: ρ)) y (Hne y _ Hy))
      as (_ & _ & ->).
    rewrite (Al y Hy). cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct v as [| | |l]; try contradiction. cbn. unfold arr_image. cbn.
    rewrite ?String.eqb_refl. cbn. rewrite ?String.eqb_refl. now rewrite ?String.eqb_refl.
Qed.

(** The refinement of a result at [return a]. *)
Lemma ret_inst_hold : forall Γ ρ a T v ψ,
  env_ok ρ Γ -> atom_ty Γ a = Some T -> eval_atom ρ a = Some v -> ~ In nu (map fst Γ) ->
  scoped (Γ ++ [(nu, T)]) ψ ->
  hold ρ (ret_inst T a ψ) <-> hold ((nu, v) :: ρ) ψ.
Proof.
  intros Γ ρ a T v ψ Hρ Ha Hv Hnu Hp. unfold hold, ret_inst. rewrite holds_subst.
  apply (holds_agree_ctx (Γ ++ [(nu, T)]) _ _ ψ Hp).
  unfold agree_ctx. rewrite !names_of_app.
  assert (Hne : forall y T', In y (names_of T' Γ) -> y <> nu)
    by (intros y T' Hy ->; apply Hnu; eapply names_of_dom; exact Hy).
  split; [ | split]; intros y Hy; apply in_app_or in Hy as [Hy | Hy].
  - destruct (bind_atom_other nu T a subst_empty (val_of_env ρ) y (Hne y _ Hy)) as (-> & _ & _).
    cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct (atom_int Γ ρ a Hρ Ha) as (z & Ez & Hz). rewrite Hv in Ez. injection Ez as ->.
    cbn. rewrite ?String.eqb_refl. exact Hz.
  - destruct (bind_atom_other nu T a subst_empty (val_of_env ρ) y (Hne y _ Hy)) as (_ & -> & _).
    cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct (atom_bool Γ ρ a Hρ Ha) as (c & Ec & Hc). rewrite Hv in Ec. injection Ec as ->.
    cbn. rewrite ?String.eqb_refl. exact Hc.
  - destruct (bind_atom_other nu T a subst_empty (val_of_env ρ) y (Hne y _ Hy)) as (_ & _ & ->).
    cbn. unfold arr_image. cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct (atom_arr Γ ρ a Hρ Ha) as (w & l & -> & Ew & Hw). rewrite Hv in Ew. injection Ew as ->.
    cbn. unfold arr_image. cbn. rewrite ?String.eqb_refl, Hw. reflexivity.
Qed.

(** ** Conditions *)

Lemma cond_hold : forall Γ ρ c b, env_ok ρ Γ -> cond_ok Γ c = true -> eval_cond ρ c = Some b ->
  (hold ρ (cond_formula c) <-> b = true).
Proof.
  intros Γ ρ c b Hρ Hc He. unfold hold. destruct c as [a | c a1 a2]; cbn in Hc; apply args_ok_atoms_ty in Hc; cbn in Hc.
  - destruct (atom_ty Γ a) as [T | ] eqn:Ea; [ | discriminate Hc]. injection Hc as ->.
    destruct (atom_bool Γ ρ a Hρ Ea) as (c & Ec & Hcv). cbn in He. rewrite Ec in He. injection He as ->.
    cbn. now rewrite Hcv.
  - destruct (atom_ty Γ a1) as [T1 | ] eqn:E1; [ | discriminate Hc].
    destruct (atom_ty Γ a2) as [T2 | ] eqn:E2; [ | discriminate Hc]. injection Hc as -> ->.
    destruct (atom_int Γ ρ a1 Hρ E1) as (z1 & F1 & H1).
    destruct (atom_int Γ ρ a2 Hρ E2) as (z2 & F2 & H2).
    cbn in He. rewrite F1, F2 in He. injection He as <-.
    destruct c; cbn; rewrite H1, H2; [apply iff_sym, Z.ltb_lt | apply iff_sym, Z.leb_le | apply iff_sym, Z.eqb_eq].
Qed.

Lemma scoped_intro : forall Γ p,
  incl (fvars p) (names_of TyInt Γ) -> incl (fbvars p) (names_of TyBool Γ) -> incl (flens p) (names_of TyArr Γ) ->
  kappas_ok [] p = true -> scoped Γ p.
Proof.
  intros Γ p H1 H2 H3 H4. unfold scoped, formula_ok. cbn.
  rewrite (proj2 (subset_In _ _) H1), (proj2 (subset_In _ _) H2), (proj2 (subset_In _ _) H3), H4. reflexivity.
Qed.

Lemma lookup_names_of : forall Γ y T, lookup y Γ = Some T -> In y (names_of T Γ).
Proof.
  intros Γ y T. unfold names_of. induction Γ as [|[z U] Γ' IH]; cbn; [discriminate 1 | ].
  destruct (String.eqb_spec y z) as [-> | ]; intros H.
  - injection H as HU. subst. unfold ty_eqb.
    match goal with |- context [ty_eq_dec ?A ?A] => destruct (ty_eq_dec A A); [now left | congruence] end.
  - destruct (ty_eqb U T); [right | ]; auto.
Qed.

Lemma cond_scoped : forall Γ c, cond_ok Γ c = true -> scoped Γ (cond_formula c).
Proof.
  intros Γ c Hc.
  assert (Ht : forall a, atom_ty Γ a = Some TyInt -> incl (tvars (aterm a)) (names_of TyInt Γ)).
  { intros a Ea y Hy. destruct a; cbn in Hy; try contradiction. destruct Hy as [<- | []].
    exact (lookup_names_of Γ _ _ Ea). }
  assert (Hl : forall a, tlens (aterm a) = []) by (intros []; reflexivity).
  destruct c as [a | c a1 a2]; cbn in Hc; apply args_ok_atoms_ty in Hc; cbn in Hc.
  - destruct (atom_ty Γ a) as [T | ] eqn:Ea; [ | discriminate Hc]. injection Hc as ->.
    apply scoped_intro; cbn; try (intros y []); try reflexivity.
    destruct a; cbn; intros y Hy; try contradiction. destruct Hy as [<- | []]. exact (lookup_names_of Γ _ _ Ea).
  - destruct (atom_ty Γ a1) as [T1 | ] eqn:E1; [ | discriminate Hc].
    destruct (atom_ty Γ a2) as [T2 | ] eqn:E2; [ | discriminate Hc]. injection Hc as -> ->.
    destruct c; apply scoped_intro; cbn; rewrite ?Hl; cbn; try (intros y []); try reflexivity;
      intros y Hy; apply in_app_or in Hy as [Hy | Hy]; first [exact (Ht a1 E1 y Hy) | exact (Ht a2 E2 y Hy)].
Qed.

(** ** The contracts of the primitives agree with their semantics *)

Lemma prim_params_sig : forall p, map snd (prim_params p) = fst (prim_sig p).
Proof. destruct p; reflexivity. Qed.

Lemma prim_params_nodup : forall p, NoDup (map fst (prim_params p)).
Proof. destruct p; cbn; repeat constructor; cbn; intuition discriminate. Qed.

Lemma prim_params_nu : forall p, ~ In nu (map fst (prim_params p)).
Proof. destruct p; cbn; intuition discriminate. Qed.

Lemma prim_contract_ok : forall p, contract_ok [] (prim_params p) (snd (prim_sig p)) (prim_contract p) = true.
Proof. destruct p; reflexivity. Qed.

Theorem prim_spec_sound : forall p vs ρp,
  Forall2 has_ty vs (fst (prim_sig p)) -> bind_params (prim_params p) vs = Some ρp ->
  Forall (hold ρp) (c_pre (prim_contract p)) ->
  exists v, eval_prim p vs = Ok v /\ has_ty v (snd (prim_sig p)) /\ hold ((nu, v) :: ρp) (c_post (prim_contract p)).
Proof.
  intros p vs ρp Hty Hb Hpre.
  destruct p; cbn in Hty;
    repeat match goal with
           | H : Forall2 _ _ (_ :: _) |- _ => inversion H; subst; clear H
           | H : Forall2 _ _ [] |- _ => inversion H; subst; clear H
           end;
    repeat match goal with v : value |- _ => destruct v; cbn in *; try contradiction end;
    cbn in Hb; injection Hb as <-.
  - eexists. split; [reflexivity | split; [exact I | ]]. unfold hold. cbn. reflexivity.
  - eexists. split; [reflexivity | split; [exact I | ]]. unfold hold. cbn. reflexivity.
  - eexists. split; [reflexivity | split; [exact I | ]]. unfold hold. cbn. split; [reflexivity | lia].
  - inversion Hpre as [|? ? _ Hp2]; subst. inversion Hp2 as [|? ? Hp _]; subst.
    unfold hold in Hp. cbn in Hp. destruct Hp as [Hlo Hhi].
    unfold get_at. rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi). cbn.
    eexists. split; [reflexivity | split; [exact I | ]]. unfold hold. reflexivity.
Qed.

(** ** Scopes of contracts *)

Lemma pres_ok_scoped : forall seen ps pres, pres_ok [] seen ps pres = true -> Forall (scoped (seen ++ ps)) pres.
Proof.
  intros seen ps. revert seen. induction ps as [|p ps IH]; intros seen [|q pres] H; cbn in H; try discriminate H.
  - constructor.
  - apply andb_prop in H as [Hq H]. constructor.
    + apply (scoped_mono (seen ++ [p])); [ | exact Hq].
      intros T y. rewrite !names_of_app. intros Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app; [left; exact Hy | ].
      right. unfold names_of in *. cbn in *. destruct (ty_eqb (snd p) T); [ | destruct Hy].
      destruct Hy as [<- | []]. now left.
    + specialize (IH (seen ++ [p]) pres H). now rewrite <- app_assoc in IH.
Qed.

Lemma contract_ok_scoped : forall ps ret c, contract_ok [] ps ret c = true ->
  Forall (scoped ps) (c_pre c) /\ scoped (ps ++ [(nu, ret)]) (c_post c).
Proof.
  intros ps ret c H. unfold contract_ok in H. apply andb_prop in H as [H1 H2].
  split; [exact (pres_ok_scoped [] ps _ H1) | exact H2].
Qed.

Lemma extend_Forall : forall (P : formula -> Prop) φ h,
  Forall P φ -> (is_ftrue h = false -> P h) -> Forall P (extend φ h).
Proof.
  intros P φ h H Hh. unfold extend. destruct (is_ftrue h) eqn:E; [exact H | ].
  apply Forall_app. split; [exact H | constructor; [exact (Hh eq_refl) | constructor]].
Qed.

Lemma fold_extend_Forall : forall (P : formula -> Prop) l acc,
  Forall P acc -> Forall P l -> Forall P (fold_left extend l acc).
Proof.
  intros P l. induction l as [|h l IH]; intros acc Hacc Hl; cbn; [exact Hacc | ].
  inversion Hl; subst. apply IH; [ | assumption]. apply extend_Forall; auto.
Qed.

Lemma pre_inst_hold : forall Γ ρ ps args vs ρf c,
  NoDup (map fst ps) -> env_ok ρ Γ -> atoms_ty Γ args = Some (map snd ps) ->
  eval_atoms ρ args = Some vs -> bind_params ps vs = Some ρf -> Forall (scoped ps) (c_pre c) ->
  hold ρ (pre_inst c ps args) -> Forall (hold ρf) (c_pre c).
Proof.
  intros Γ ρ ps args vs ρf c Hnd Hρ Ha He Hb Hs H. unfold hold, pre_inst in H.
  rewrite holds_fconj, Forall_map in H. apply Forall_forall. intros q Hq.
  apply (inst_pre Γ ρ ps args vs ρf q Hnd Hρ Ha He Hb (proj1 (Forall_forall _ _) Hs q Hq)).
  exact (proj1 (Forall_forall _ _) H q Hq).
Qed.

Lemma atom_var_names : forall Γ a T y, atom_ty Γ a = Some T -> a = AVar y -> In y (names_of T Γ).
Proof. intros Γ a T y Ha ->. exact (lookup_names_of Γ y T Ha). Qed.

Lemma aterm_scope : forall Γ a, atom_ty Γ a = Some TyInt -> incl (tvars (aterm a)) (names_of TyInt Γ) /\ tlens (aterm a) = [].
Proof.
  intros Γ a Ha. destruct a; cbn in Ha |- *; try discriminate Ha.
  - split; [intros y [<- | []]; exact (lookup_names_of Γ _ _ Ha) | reflexivity].
  - split; [intros y [] | reflexivity].
Qed.

Lemma abatom_scope : forall Γ a, atom_ty Γ a = Some TyBool -> incl (bvars (abatom a)) (names_of TyBool Γ).
Proof.
  intros Γ a Ha. destruct a; cbn in Ha |- *; try discriminate Ha.
  - intros y [<- | []]. exact (lookup_names_of Γ _ _ Ha).
  - intros y [].
Qed.

Lemma s_int_bind : forall p T a σ y, assoc y (s_int (bind_atom p T a σ)) =
  match T with TyInt => if String.eqb y p then Some (aterm a) else assoc y (s_int σ) | _ => assoc y (s_int σ) end.
Proof. intros. destruct T, a; reflexivity. Qed.

Lemma s_bool_bind : forall p T a σ y, assoc y (s_bool (bind_atom p T a σ)) =
  match T with TyBool => if String.eqb y p then Some (abatom a) else assoc y (s_bool σ) | _ => assoc y (s_bool σ) end.
Proof. intros. destruct T, a; reflexivity. Qed.

Lemma arr_image_bind : forall p T a σ y, arr_image (bind_atom p T a σ) y =
  match T, a with TyArr, AVar w => if String.eqb y p then w else arr_image σ y | _, _ => arr_image σ y end.
Proof. intros. destruct T, a; try reflexivity. unfold arr_image. cbn. destruct (String.eqb y p); reflexivity. Qed.

Lemma inst_scope : forall Γ ps args, atoms_ty Γ args = Some (map snd ps) ->
  (forall y, In y (names_of TyInt ps) -> exists t, assoc y (s_int (inst_subst ps args)) = Some t /\
                                                   incl (tvars t) (names_of TyInt Γ) /\ tlens t = []) /\
  (forall y, In y (names_of TyBool ps) -> exists b, assoc y (s_bool (inst_subst ps args)) = Some b /\
                                                    incl (bvars b) (names_of TyBool Γ)) /\
  (forall y, In y (names_of TyArr ps) -> In (arr_image (inst_subst ps args) y) (names_of TyArr Γ)).
Proof.
  intros Γ ps. induction ps as [|[p T] ps IH]; intros args Ha.
  - split; [ | split]; intros y [].
  - destruct args as [|a args]; [discriminate Ha | ]. cbn in Ha.
    destruct (atom_ty Γ a) as [U | ] eqn:Ea; [ | discriminate Ha].
    destruct (atoms_ty Γ args) as [Us | ] eqn:Eas; [ | discriminate Ha]. injection Ha as HU HUs. subst U Us.
    destruct (IH args Eas) as (IHi & IHb & IHa). cbn [inst_subst].
    split; [ | split]; intros y Hy; rewrite ?s_int_bind, ?s_bool_bind, ?arr_image_bind;
      apply names_of_cons_inv in Hy as [[-> ->] | Hy].
    + rewrite String.eqb_refl. exists (aterm a). split; [reflexivity | exact (aterm_scope Γ a Ea)].
    + destruct (IHi y Hy) as (t & Et & Ht).
      destruct T; try (exists t; split; [exact Et | exact Ht]).
      destruct (String.eqb y p); [exists (aterm a); split; [reflexivity | exact (aterm_scope Γ a Ea)] | ].
      exists t. split; [exact Et | exact Ht].
    + rewrite String.eqb_refl. exists (abatom a). split; [reflexivity | exact (abatom_scope Γ a Ea)].
    + destruct (IHb y Hy) as (b & Eb & Hb).
      destruct T; try (exists b; split; [exact Eb | exact Hb]).
      destruct (String.eqb y p); [exists (abatom a); split; [reflexivity | exact (abatom_scope Γ a Ea)] | ].
      exists b. split; [exact Eb | exact Hb].
    + destruct a; cbn in Ea; try discriminate Ea. rewrite String.eqb_refl. exact (lookup_names_of Γ _ _ Ea).
    + specialize (IHa y Hy). destruct T, a; try exact IHa.
      destruct (String.eqb y p); [exact (lookup_names_of Γ _ _ Ea) | exact IHa].
Qed.

Lemma post_inst_scoped : forall Γ ps args T x c,
  ~ In nu (map fst ps) -> atoms_ty Γ args = Some (map snd ps) -> scoped (ps ++ [(nu, T)]) (c_post c) ->
  scoped ((x, T) :: Γ) (post_inst c ps T args x).
Proof.
  intros Γ ps args T x c Hnu Ha Hp. unfold scoped, post_inst.
  apply formula_ok_subst with (sc := scope_of (ps ++ [(nu, T)])); [ | exact Hp].
  destruct (inst_scope Γ ps args Ha) as (Hi & Hb & Har).
  assert (Hne : forall y T', In y (names_of T' ps) -> y <> nu)
    by (intros y T' Hy ->; apply Hnu; eapply names_of_dom; exact Hy).
  assert (Hself : forall U, In x (names_of U ((x, U) :: Γ))).
  { intros U. unfold names_of. cbn. unfold ty_eqb.
    destruct (ty_eq_dec U U); [now left | congruence]. }
  unfold res_subst. split; [ | split]; cbn [sc_int sc_bool sc_arr scope_of]; intros y Hy;
    rewrite names_of_app in Hy; apply in_app_or in Hy as [Hy | Hy].
  - destruct (Hi y Hy) as (t & Et & Ht1 & Ht2).
    assert (E : assoc y (s_int (bind_atom nu T (AVar x) (inst_subst ps args))) = Some t).
    { destruct T; cbn; try exact Et. rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)). exact Et. }
    rewrite E. split; [intros z Hz; apply names_of_cons, Ht1, Hz | rewrite Ht2; intros z []].
  - apply names_of_cons_inv in Hy as [[-> ->] | []]. cbn.
    split; [intros z [<- | []]; first [apply Hself | left; reflexivity] | intros z []].
  - destruct (Hb y Hy) as (b & Eb & Hb').
    assert (E : assoc y (s_bool (bind_atom nu T (AVar x) (inst_subst ps args))) = Some b).
    { destruct T; cbn; try exact Eb. rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)). exact Eb. }
    rewrite E. intros z Hz. apply names_of_cons, Hb', Hz.
  - apply names_of_cons_inv in Hy as [[-> ->] | []]. cbn.
    intros z [<- | []]. first [apply Hself | left; reflexivity].
  - specialize (Har y Hy). unfold arr_image in *.
    destruct T; cbn; try rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)); first [exact Har | right; exact Har | apply names_of_cons; exact Har].
  - apply names_of_cons_inv in Hy as [[-> ->] | []]. unfold arr_image. cbn. first [apply Hself | left; reflexivity].
Qed.

(** ** The induction on fuel *)

Lemma emit_hold : forall l φ g ρ, (forall ob, In ob (emit l φ g) -> valid ob) -> Forall (hold ρ) φ -> hold ρ g.
Proof.
  intros l φ g ρ Hv Hφ. unfold emit in Hv. destruct (is_ftrue g) eqn:E; [apply is_ftrue_holds, E | ].
  exact (Hv _ (or_introl eq_refl) no_kappa (val_of_env ρ) (val_of_env_lens ρ) Hφ).
Qed.

Lemma bind_params_env_ok : forall ps vs ρf, bind_params ps vs = Some ρf -> Forall2 has_ty vs (map snd ps) -> env_ok ρf ps.
Proof.
  intros ps vs ρf Hb Hvs. destruct (bind_params_typed ps vs Hvs) as (ρ' & E & H).
  rewrite Hb in E. injection E as <-. exact H.
Qed.

Lemma distinct_NoDup : forall xs, distinct xs = true -> NoDup xs.
Proof.
  intros xs. induction xs as [|x xs IH]; cbn; intros H; [constructor | ].
  apply andb_prop in H as [H1 H2]. constructor; [ | exact (IH H2)].
  intros Hin. rewrite negb_true_iff in H1. assert (existsb (String.eqb x) xs = true); [ | congruence].
  apply existsb_exists. exists x. split; [exact Hin | apply String.eqb_refl].
Qed.

Lemma not_reserved_nu : forall xs, forallb (fun x => negb (reserved x)) xs = true -> ~ In nu xs.
Proof.
  intros xs H Hin. rewrite forallb_forall in H. specialize (H nu Hin). unfold reserved in H.
  rewrite String.eqb_refl in H. discriminate H.
Qed.

Lemma fresh_ok_inv : forall Γ x, fresh_ok Γ x = true -> lookup x Γ = None /\ x <> nu.
Proof.
  intros Γ x H. unfold fresh_ok in H. apply andb_prop in H as [H1 H2].
  split; [destruct (lookup x Γ); [discriminate H2 | reflexivity] | ].
  intros ->. unfold reserved in H1. rewrite String.eqb_refl in H1. discriminate H1.
Qed.

Lemma not_in_cons : forall x (T : ty) (Γ : tenv), x <> nu -> ~ In nu (map fst Γ) -> ~ In nu (map fst ((x, T) :: Γ)).
Proof. intros x T Γ H1 H2 [E | E]; [cbn in E; congruence | exact (H2 E)]. Qed.

Lemma answer_ok_fresh : forall Γ ρ x v T ψ a,
  lookup x Γ = None -> x <> nu -> scoped (Γ ++ [(nu, T)]) ψ ->
  answer_ok a ((x, v) :: ρ) ψ -> answer_ok a ρ ψ.
Proof.
  intros Γ ρ x v T ψ a Hx Hn Hψ H. destruct a as [w | | ]; cbn in *; auto.
  exact (proj1 (hold_fresh_nu Γ ρ x v w T ψ Hx Hn Hψ) H).
Qed.

Lemma scoped_not : forall Γ p, scoped Γ p -> scoped Γ (FNot p).
Proof. intros Γ p H. exact H. Qed.

Section Guarantee.
  Variable P : prog.
  Variable Sp : spec.
  Hypothesis HP : ty_prog P = Ok tt.
  Hypothesis HS : spec_ok [] P Sp = true.
  Hypothesis Hvalid : forall ob, In ob (prog_obligations RuleName P Sp) -> valid ob.

  Definition fun_ok (k : nat) : Prop :=
    forall fd vs ρf, In fd P -> bind_params (fd_params fd) vs = Some ρf ->
      Forall2 has_ty vs (map snd (fd_params fd)) ->
      Forall (hold ρf) (c_pre (contract_of Sp fd)) ->
      answer_ok (evalFuel k P ρf (fd_body fd)) ρf (c_post (contract_of Sp fd)).

  Definition expr_ok (k : nat) : Prop :=
    forall scope Γ φ e ψ T ρ,
      ty_expr P Γ e = Ok T -> env_ok ρ Γ -> ~ In nu (map fst Γ) ->
      Forall (scoped Γ) φ -> scoped (Γ ++ [(nu, T)]) ψ ->
      (forall ob, In ob (gen RuleName P Sp scope Γ φ e ψ) -> valid ob) ->
      Forall (hold ρ) φ ->
      answer_ok (evalFuel k P ρ e) ρ ψ.

  Lemma fun_contract_ok : forall fd, In fd P -> contract_ok [] (fd_params fd) (fd_ret fd) (contract_of Sp fd) = true.
  Proof.
    intros fd Hin. unfold spec_ok in HS. apply andb_prop in HS as [_ H]. rewrite forallb_forall in H. exact (H fd Hin).
  Qed.

  Lemma fun_typed : forall fd, In fd P ->
    NoDup (map fst (fd_params fd)) /\ ~ In nu (map fst (fd_params fd)) /\
    ty_expr P (fd_params fd) (fd_body fd) = Ok (fd_ret fd).
  Proof.
    intros fd Hin. pose proof (ty_prog_fun P fd HP Hin) as H. unfold ty_fun in H.
    bind_in H u1 H1. bind_in H u2 H2. bind_in H T HT.
    apply require_ok, ty_eqb_eq in H. subst T.
    split; [exact (distinct_NoDup _ (require_ok _ _ _ H1)) | ].
    split; [exact (not_reserved_nu _ (require_ok _ _ _ H2)) | exact HT].
  Qed.

  (** Extending by the result of a primitive or of a call. *)
  Lemma continue_ok : forall k scope Γ φ x Tx v h e' ψ T ρ,
    expr_ok k ->
    ty_expr P ((x, Tx) :: Γ) e' = Ok T -> env_ok ρ Γ -> ~ In nu (map fst Γ) ->
    lookup x Γ = None -> x <> nu -> has_ty v Tx ->
    Forall (scoped Γ) φ -> scoped ((x, Tx) :: Γ) h -> scoped (Γ ++ [(nu, T)]) ψ ->
    (forall ob, In ob (gen RuleName P Sp scope ((x, Tx) :: Γ) (extend φ h) e' ψ) -> valid ob) ->
    Forall (hold ρ) φ -> hold ((x, v) :: ρ) h ->
    answer_ok (evalFuel k P ((x, v) :: ρ) e') ρ ψ.
  Proof.
    intros k scope Γ φ x Tx v h e' ψ T ρ He Ht Hρ Hnu Hx Hxn Hv Hφs Hhs Hψs Hval Hφ Hh.
    apply (answer_ok_fresh Γ ρ x v T ψ _ Hx Hxn Hψs).
    eapply He; [exact Ht | apply env_ok_cons; [ | exact Hv] | apply not_in_cons; auto | | | exact Hval | ].
    - exact Hρ.
    - apply extend_Forall; [ | intros _; exact Hhs].
      eapply Forall_impl; [ | exact Hφs]. intros q Hq. apply scoped_cons, Hq.
    - apply scoped_cons_nu, Hψs.
    - apply extend_Forall; [ | intros _; exact Hh].
      apply Forall_forall. intros q Hq.
      apply (proj2 (hold_fresh Γ ρ x v q Hx (proj1 (Forall_forall _ _) Hφs q Hq))).
      exact (proj1 (Forall_forall _ _) Hφ q Hq).
  Qed.

  Lemma expr_ok_step : forall k, fun_ok k -> expr_ok k -> expr_ok (S k).
  Proof.
    intros k Hf He scope Γ φ e ψ T ρ Ht Hρ Hnu Hφs Hψs Hv Hφ.
    destruct e as [a | x p args e' | x f args e' | c e1 e2]; cbn [evalFuel]; cbn in Ht.
    - destruct (atom_ty Γ a) as [T' | ] eqn:Ea; [ | discriminate Ht]. injection Ht as <-.
      destruct (eval_atom_typed ρ Γ a T' Hρ Ea) as (v & Ev & _). rewrite Ev. cbn.
      cbn [gen] in Hv. unfold atom_type in Hv. rewrite Ea in Hv.
      apply (ret_inst_hold Γ ρ a T' v ψ Hρ Ea Ev Hnu Hψs). exact (emit_hold _ _ _ _ Hv Hφ).
    - bind_in Ht u1 H1. bind_in Ht u2 H2.
      apply require_ok, args_ok_atoms_ty in H1. apply require_ok, fresh_ok_inv in H2 as [Hx Hxn].
      rewrite <- prim_params_sig in H1.
      destruct (eval_atoms_typed ρ Γ args _ Hρ H1) as (vs & Evs & Hvs). rewrite Evs.
      destruct (bind_params_typed (prim_params p) vs Hvs) as (ρp & Eρp & _).
      cbn [gen] in Hv.
      assert (Hpre : hold ρ (pre_inst (prim_contract p) (prim_params p) args)).
      { apply (emit_hold _ _ _ _ (fun ob H => Hv ob (in_or_app _ _ _ (or_introl H))) Hφ). }
      pose proof (contract_ok_scoped _ _ _ (prim_contract_ok p)) as [Hpres Hposts].
      pose proof (pre_inst_hold Γ ρ _ args vs ρp _ (prim_params_nodup p) Hρ H1 Evs Eρp Hpres Hpre) as Hpre'.
      rewrite prim_params_sig in Hvs.
      destruct (prim_spec_sound p vs ρp Hvs Eρp Hpre') as (v & -> & Hvt & Hpost).
      rewrite <- prim_params_sig in Hvs.
      eapply continue_ok with (scope := scope); [exact He | exact Ht | exact Hρ | exact Hnu | exact Hx | exact Hxn | exact Hvt
                          | exact Hφs | | exact Hψs | | exact Hφ | ].
      + apply post_inst_scoped; [apply prim_params_nu | exact H1 | exact Hposts].
      + intros ob H. apply Hv, in_or_app. now right.
      + apply (proj2 (inst_post Γ ρ _ args vs ρp _ x v _ (prim_params_nodup p) (prim_params_nu p) Hρ H1 Evs Eρp
                                Hx Hxn Hvt Hposts)).
        exact Hpost.
    - destruct (find_fun f P) as [fd | ] eqn:Ef; [ | discriminate Ht].
      bind_in Ht u1 H1. bind_in Ht u2 H2.
      apply require_ok, args_ok_atoms_ty in H1. apply require_ok, fresh_ok_inv in H2 as [Hx Hxn].
      pose proof (find_fun_in _ _ _ Ef) as Hin.
      destruct (fun_typed fd Hin) as (Hnd & Hfnu & Hbody).
      destruct (eval_atoms_typed ρ Γ args _ Hρ H1) as (vs & Evs & Hvs). rewrite Evs.
      destruct (bind_params_typed (fd_params fd) vs Hvs) as (ρf & Eρf & Hρf). rewrite Eρf.
      cbn [gen] in Hv. rewrite Ef in Hv.
      assert (Hpre : hold ρ (pre_inst (contract_of Sp fd) (fd_params fd) args)).
      { apply (emit_hold _ _ _ _ (fun ob H => Hv ob (in_or_app _ _ _ (or_introl H))) Hφ). }
      pose proof (contract_ok_scoped _ _ _ (fun_contract_ok fd Hin)) as [Hpres Hposts].
      pose proof (pre_inst_hold Γ ρ _ args vs ρf _ Hnd Hρ H1 Evs Eρf Hpres Hpre) as Hpre'.
      pose proof (Hf fd vs ρf Hin Eρf Hvs Hpre') as Hans.
      destruct (eval_typed k P ρf (fd_params fd) (fd_body fd) (fd_ret fd) HP Hρf Hbody)
        as [Ea | [(v & Ea & Hvt) | (l & i & n & Ea)]]; rewrite Ea in Hans |- *; cbn in Hans; [exact I | | contradiction].
      eapply continue_ok with (scope := scope); [exact He | exact Ht | exact Hρ | exact Hnu | exact Hx | exact Hxn | exact Hvt
                          | exact Hφs | | exact Hψs | | exact Hφ | ].
      + apply post_inst_scoped; [exact Hfnu | exact H1 | exact Hposts].
      + intros ob H. apply Hv, in_or_app. now right.
      + apply (proj2 (inst_post Γ ρ _ args vs ρf _ x v _ Hnd Hfnu Hρ H1 Evs Eρf Hx Hxn Hvt Hposts)).
        exact Hans.
    - bind_in Ht u1 H1. bind_in Ht T1 HT1. bind_in Ht T2 HT2. bind_in Ht u2 H2. injection Ht as <-.
      apply require_ok in H1. apply require_ok, ty_eqb_eq in H2. subst T2.
      destruct (eval_cond_typed ρ Γ c Hρ H1) as (b & Eb). rewrite Eb.
      pose proof (cond_hold Γ ρ c b Hρ H1 Eb) as Hc.
      cbn [gen] in Hv.
      destruct b.
      + eapply He with (scope := scope); [exact HT1 | exact Hρ | exact Hnu | | exact Hψs | | ].
        * apply extend_Forall; [exact Hφs | intros _; apply cond_scoped, H1].
        * intros ob H. apply Hv, in_or_app. now left.
        * apply extend_Forall; [exact Hφ | intros _; apply Hc; reflexivity].
      + eapply He with (scope := scope); [exact HT2 | exact Hρ | exact Hnu | | exact Hψs | | ].
        * apply extend_Forall; [exact Hφs | intros _; apply scoped_not, cond_scoped, H1].
        * intros ob H. apply Hv, in_or_app. now right.
        * apply extend_Forall; [exact Hφ | intros _]. intros H. apply Hc in H. discriminate H.
  Qed.

  Lemma fun_ok_of_expr : forall k, expr_ok k -> fun_ok k.
  Proof.
    intros k He fd vs ρf Hin Hb Hvs Hpre.
    destruct (fun_typed fd Hin) as (Hnd & Hfnu & Hbody).
    pose proof (contract_ok_scoped _ _ _ (fun_contract_ok fd Hin)) as [Hpres Hposts].
    eapply He with (scope := fd_name fd) (φ := pre_hyps (contract_of Sp fd));
      [exact Hbody | exact (bind_params_env_ok _ _ _ Hb Hvs) | exact Hfnu | | exact Hposts | | ].
    - apply fold_extend_Forall; [constructor | exact Hpres].
    - intros ob H. apply Hvalid. unfold prog_obligations. apply in_flat_map. exists fd. split; [exact Hin | exact H].
    - apply fold_extend_Forall; [constructor | exact Hpre].
  Qed.

  Theorem guarantee : forall k, fun_ok k /\ expr_ok k.
  Proof.
    induction k as [|k [Hf He]].
    - split.
      + intros fd vs ρf _ _ _ _. exact I.
      + intros scope Γ φ e ψ T ρ _ _ _ _ _ _ _. exact I.
    - assert (He' : expr_ok (S k)) by exact (expr_ok_step k Hf He).
      split; [exact (fun_ok_of_expr (S k) He') | exact He'].
  Qed.
End Guarantee.

(** ** The contracts *)

Lemma accepted_valid : forall {C} (oracle : obligation -> verdict C) P S,
  oracle_sound oracle -> accepted (check_prog oracle P S) = true ->
  ty_prog P = Ok tt /\ spec_ok [] P S = true /\ (forall ob, In ob (prog_obligations RuleName P S) -> valid ob).
Proof.
  intros C oracle P S Ho H. unfold accepted, check_prog, check_prog_with in H.
  destruct (ty_prog P) as [[] | e] eqn:Ep; [ | discriminate H]. cbn in H.
  destruct (spec_ok [] P S) eqn:Es; [ | discriminate H]. cbn in H.
  split; [reflexivity | split; [reflexivity | ]].
  intros ob Hin. apply (oracle_proved oracle ob Ho).
  unfold all_proved, judge in H. rewrite forallb_forall in H.
  exact (H (ob, oracle ob) (in_map (fun ob => (ob, oracle ob)) _ _ Hin)).
Qed.

Theorem check_prog_sound : forall {C} (oracle : obligation -> verdict C) P S,
  oracle_sound oracle -> accepted (check_prog oracle P S) = true ->
  forall k fd vs ρf, In fd P -> bind_params (fd_params fd) vs = Some ρf ->
    Forall2 has_ty vs (map snd (fd_params fd)) ->
    Forall (hold ρf) (c_pre (contract_of S fd)) ->
    answer_ok (evalFuel k P ρf (fd_body fd)) ρf (c_post (contract_of S fd)).
Proof.
  intros C oracle P S Ho H k. destruct (accepted_valid oracle P S Ho H) as (HP & HS & Hv).
  exact (proj1 (guarantee P S HP HS Hv k)).
Qed.

Theorem check_client_sound : forall {C} (oracle : obligation -> verdict C) P S cl,
  oracle_sound oracle -> accepted (check_prog oracle P S) = true -> accepted (check_client oracle P S cl) = true ->
  forall ρ, env_ok ρ (cl_env cl) -> Forall (hold ρ) (cl_pre cl) ->
  forall k, answer_ok (evalFuel k P ρ (cl_expr cl)) ρ (cl_post cl).
Proof.
  intros C oracle P S cl Ho Hp Hc ρ Hρ Hpre k.
  destruct (accepted_valid oracle P S Ho Hp) as (HP & HS & Hv).
  unfold accepted, check_client, check_client_with in Hc. rewrite HP in Hc. cbn in Hc. rewrite HS in Hc. cbn in Hc.
  destruct (client_ok [] P cl) as [T | e] eqn:Ecl; [ | discriminate Hc]. cbn in Hc.
  unfold client_ok in Ecl. bind_in Ecl u1 H1. bind_in Ecl T' HT. bind_in Ecl u2 H2. injection Ecl as <-.
  apply require_ok, andb_prop in H1 as [_ H1]. apply require_ok, andb_prop in H2 as [H2 H3].
  rewrite forallb_forall in H2.
  eapply (proj2 (guarantee P S HP HS Hv k)) with (scope := client_scope) (φ := fold_left extend (cl_pre cl) []);
    [exact HT | exact Hρ | exact (not_reserved_nu _ H1) | | exact H3 | | ].
  - apply fold_extend_Forall; [constructor | apply Forall_forall; exact H2].
  - intros ob Hin. apply (oracle_proved oracle ob Ho).
    unfold all_proved, judge in Hc. rewrite forallb_forall in Hc.
    exact (Hc (ob, oracle ob) (in_map (fun ob => (ob, oracle ob)) _ _ Hin)).
  - apply fold_extend_Forall; [constructor | exact Hpre].
Qed.
