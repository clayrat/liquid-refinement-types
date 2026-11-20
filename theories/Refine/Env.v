(** * Environments as valuations, and scopes

    The link between programs and the logic, on which the operational
    guarantee (Refine/Sound.v) and the statement of the measures
    (Refine/Measure.v) rest.

    The valuation of an environment [val_of_env]: an integer variable is
    its value, a boolean one its value, an array or list name its length;
    [hold ρ p] is the truth of [p] in it, every [κ] read as false (the
    contracts of the first algorithm have none).  Its pieces:

    - [holds_lookup_agree]: a formula depends only on the bindings of its
      names; with the freshness of the names bound by [let] and the scopes
      of the formulas, the hypotheses stay true when the environment is
      extended ([hold_fresh], [hold_fresh_nu]);
    - [inst_pre] and [inst_post]: the substitution of the formal
      parameters by the actual atoms is evaluating under the environment
      of the callee, and [ν] by the name of the result is binding [ν] to
      the returned value; [ret_inst_hold] is the same for [return a];
    - [cond_hold]: the formula of a condition holds exactly when the
      condition evaluates to [true].

    The scopes: [scoped Γ p] is [formula_ok] in the scope of [Γ], that
    is, the names of [p] are bound in [Γ] with their sorts
    ([scoped_iff]).  The contracts accepted by [spec_ok], the hypotheses
    of the branches and the contracts instantiated at a call are in
    scope ([contract_ok_scoped], [cond_scoped], [len_hyp_scoped],
    [post_inst_scoped]). *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing EvalFacts.
From Liquid.Refine Require Import Spec.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ** The valuation of an environment *)

Definition val_of_env (ρ : env) : valuation :=
  mkVal (fun x => match lookup x ρ with Some (VInt z) => z | _ => 0 end)
        (fun b => match lookup b ρ with Some (VBool c) => c | _ => false end)
        (fun a => match lookup a ρ with
                  | Some (VArr l) | Some (VList l) => Z.of_nat (List.length l)
                  | _ => 0
                  end).

Lemma val_of_env_lens : forall ρ, lens_nonneg (val_of_env ρ).
Proof. intros ρ a. cbn. destruct (lookup a ρ) as [[]|]; lia. Qed.

(** The length of the array or list a name is bound to. *)
Definition vlength (v : value) : Z :=
  match v with VArr l | VList l => Z.of_nat (List.length l) | _ => 0 end.

Lemma vlen_lookup : forall ρ y v, lookup y ρ = Some v -> vlen (val_of_env ρ) y = vlength v.
Proof. intros ρ y v H. cbn. rewrite H. destruct v; reflexivity. Qed.

Definition hold (ρ : env) (p : formula) : Prop := holds no_kappa (val_of_env ρ) p.

(** ** Names of formulas *)

Definition fnames (p : formula) : list string := fvars p ++ fbvars p ++ flens p.

Lemma holds_lookup_agree : forall ρ1 ρ2 p,
  (forall y, In y (fnames p) -> lookup y ρ1 = lookup y ρ2) -> hold ρ1 p <-> hold ρ2 p.
Proof.
  intros ρ1 ρ2 p H. unfold hold. apply holds_agree. unfold agree_on, fnames in *.
  split; [ | split]; intros y Hy; cbn; rewrite H; auto; apply in_or_app; [left | right; apply in_or_app; left
                                                                         | right; apply in_or_app; right]; exact Hy.
Qed.

(** ** Names and scopes *)

Definition scoped (Γ : tenv) (p : formula) : Prop := formula_ok [] (scope_of Γ) p = true.

(** [names_of T Γ] and [names_len Γ] are the names of [Γ] filtered by
    their types. *)
Lemma filter_names_In : forall (g : string * ty -> bool) (Γ : tenv) y,
  In y (map fst (filter g Γ)) <-> exists U, In (y, U) Γ /\ g (y, U) = true.
Proof.
  intros g Γ y. rewrite in_map_iff. split.
  - intros ([z U] & <- & Hin). apply filter_In in Hin. exists U. exact Hin.
  - intros (U & Hin & Hg). exists (y, U). split; [reflexivity | apply filter_In; auto].
Qed.

Lemma names_of_iff : forall T Γ y, In y (names_of T Γ) <-> In (y, T) Γ.
Proof.
  intros T Γ y. unfold names_of. rewrite filter_names_In. cbn. split.
  - intros (U & Hin & HU). apply ty_eqb_eq in HU. subst U. exact Hin.
  - intros Hin. exists T. split; [exact Hin | apply ty_eqb_refl].
Qed.

Lemma names_len_iff : forall Γ y, In y (names_len Γ) <-> exists U, In (y, U) Γ /\ len_ty U = true.
Proof. intros Γ y. exact (filter_names_In (fun p => len_ty (snd p)) Γ y). Qed.

Lemma names_of_dom : forall T Γ y, In y (names_of T Γ) -> In y (map fst Γ).
Proof. intros T Γ y H. apply names_of_iff in H. exact (in_map fst Γ (y, T) H). Qed.

Lemma names_len_dom : forall Γ y, In y (names_len Γ) -> In y (map fst Γ).
Proof. intros Γ y H. apply names_len_iff in H as (U & H & _). exact (in_map fst Γ (y, U) H). Qed.

Lemma in_names_len : forall Γ y T, In (y, T) Γ -> len_ty T = true -> In y (names_len Γ).
Proof. intros Γ y T H HT. apply names_len_iff. eauto. Qed.

Lemma lookup_names_of : forall Γ y T, lookup y Γ = Some T -> In y (names_of T Γ).
Proof. intros Γ y T H. apply names_of_iff, lookup_In, H. Qed.

Lemma lookup_names_len : forall Γ y T, lookup y Γ = Some T -> len_ty T = true -> In y (names_len Γ).
Proof. intros Γ y T H. apply in_names_len, lookup_In, H. Qed.

Lemma names_of_app : forall T Γ1 Γ2, names_of T (Γ1 ++ Γ2) = names_of T Γ1 ++ names_of T Γ2.
Proof. intros T Γ1 Γ2. unfold names_of. now rewrite filter_app, map_app. Qed.

Lemma names_len_app : forall Γ1 Γ2, names_len (Γ1 ++ Γ2) = names_len Γ1 ++ names_len Γ2.
Proof. intros Γ1 Γ2. unfold names_len. now rewrite filter_app, map_app. Qed.

Lemma names_of_cons : forall T x U Γ y, In y (names_of T Γ) -> In y (names_of T ((x, U) :: Γ)).
Proof. intros T x U Γ y H. apply names_of_iff. right. apply names_of_iff, H. Qed.

Lemma names_len_cons : forall x U Γ y, In y (names_len Γ) -> In y (names_len ((x, U) :: Γ)).
Proof. intros x U Γ y H. apply names_len_iff in H as (V & H & HV). apply names_len_iff. exists V. split; [now right | exact HV]. Qed.

Lemma names_of_cons_inv : forall T p U Γ y, In y (names_of T ((p, U) :: Γ)) ->
  (y = p /\ U = T) \/ In y (names_of T Γ).
Proof.
  intros T p U Γ y H. rewrite !names_of_iff in *.
  destruct H as [E | H]; [injection E as -> ->; now left | now right].
Qed.

Lemma names_len_cons_inv : forall p U Γ y, In y (names_len ((p, U) :: Γ)) ->
  (y = p /\ len_ty U = true) \/ In y (names_len Γ).
Proof.
  intros p U Γ y H. apply names_len_iff in H as (V & [E | H] & HV).
  - injection E as -> ->. now left.
  - right. apply names_len_iff. eauto.
Qed.

Lemma scoped_iff : forall Γ p, scoped Γ p <->
  incl (fvars p) (names_of TyInt Γ) /\ incl (fbvars p) (names_of TyBool Γ) /\ incl (flens p) (names_len Γ) /\
  kappas_ok [] p = true.
Proof.
  intros Γ p. unfold scoped, formula_ok, incl. cbn [scope_of sc_int sc_bool sc_arr].
  rewrite !andb_true_iff, !subset_In. tauto.
Qed.

Lemma scoped_fv : forall Γ p, scoped Γ p ->
  incl (fvars p) (names_of TyInt Γ) /\ incl (fbvars p) (names_of TyBool Γ) /\ incl (flens p) (names_len Γ).
Proof. intros Γ p H. apply scoped_iff in H. tauto. Qed.

Lemma scoped_intro : forall Γ p,
  incl (fvars p) (names_of TyInt Γ) -> incl (fbvars p) (names_of TyBool Γ) -> incl (flens p) (names_len Γ) ->
  kappas_ok [] p = true -> scoped Γ p.
Proof. intros Γ p H1 H2 H3 H4. apply scoped_iff. repeat split; assumption. Qed.

Lemma scoped_names : forall Γ p, scoped Γ p -> forall y, In y (fnames p) -> In y (map fst Γ).
Proof.
  intros Γ p H y Hy. destruct (scoped_fv Γ p H) as (A & B & C). unfold fnames in Hy.
  rewrite !in_app_iff in Hy. destruct Hy as [Hy | [Hy | Hy]];
    [exact (names_of_dom _ _ _ (A y Hy)) | exact (names_of_dom _ _ _ (B y Hy)) | exact (names_len_dom _ _ (C y Hy))].
Qed.

(** A larger context keeps a formula in scope. *)
Lemma scoped_mono : forall Γ Γ' p, incl Γ Γ' -> scoped Γ p -> scoped Γ' p.
Proof.
  intros Γ Γ' p Hsub H. apply scoped_iff in H as (A & B & C & D). apply scoped_iff.
  split; [ | split; [ | split]]; [intros y Hy | intros y Hy | intros y Hy | exact D].
  - apply names_of_iff, Hsub, names_of_iff, A, Hy.
  - apply names_of_iff, Hsub, names_of_iff, B, Hy.
  - apply C, names_len_iff in Hy as (U & HU & HT). apply names_len_iff. eauto.
Qed.

Lemma scoped_cons : forall Γ x U p, scoped Γ p -> scoped ((x, U) :: Γ) p.
Proof. intros Γ x U p. apply scoped_mono. intros q Hq. now right. Qed.

Lemma scoped_cons_nu : forall Γ x U T p, scoped (Γ ++ [(nu, T)]) p -> scoped (((x, U) :: Γ) ++ [(nu, T)]) p.
Proof.
  intros Γ x U T p. apply scoped_mono. intros q Hq.
  apply in_app_or in Hq as [Hq | Hq]; apply in_or_app; [left; now right | now right].
Qed.

(** ** Extending an environment by a fresh name *)

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
  intros Γ ρ a H Ha. destruct (eval_atom_typed ρ Γ a TyInt H Ha) as ([z| | | |] & E & Hv); try contradiction.
  exists z. split; [exact E | ]. destruct a; cbn in E |- *; try discriminate E.
  - now rewrite E.
  - congruence.
Qed.

Lemma atom_bool : forall Γ ρ a, env_ok ρ Γ -> atom_ty Γ a = Some TyBool ->
  exists c, eval_atom ρ a = Some (VBool c) /\ beval (val_of_env ρ) (abatom a) = c.
Proof.
  intros Γ ρ a H Ha. destruct (eval_atom_typed ρ Γ a TyBool H Ha) as ([|c| | |] & E & Hv); try contradiction.
  exists c. split; [exact E | ]. destruct a; cbn in E |- *; try discriminate E.
  - now rewrite E.
  - congruence.
Qed.

Lemma atom_len : forall Γ ρ a T, env_ok ρ Γ -> atom_ty Γ a = Some T -> len_ty T = true ->
  exists y v, a = AVar y /\ eval_atom ρ a = Some v /\ lookup y ρ = Some v.
Proof.
  intros Γ ρ a T H Ha HT. destruct (eval_atom_typed ρ Γ a T H Ha) as (v & E & Hv).
  destruct a; cbn in E, Ha; try (injection Ha as <-; discriminate HT). exists x, v. auto.
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
  agree_on (names_of TyInt Γ) (names_of TyBool Γ) (names_len Γ) ρ1 ρ2.


Lemma holds_agree_ctx : forall Γ ρ1 ρ2 p, scoped Γ p -> agree_ctx Γ ρ1 ρ2 ->
  holds no_kappa ρ1 p <-> holds no_kappa ρ2 p.
Proof.
  intros Γ ρ1 ρ2 p Hp H. apply holds_agree. destruct (scoped_fv Γ p Hp) as (A & B & C).
  exact (agree_on_incl _ _ _ _ _ _ _ _ H A B C).
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
    split; [ | split]; intros y Hy;
      [apply names_of_cons_inv in Hy as [[-> ->] | Hy] | apply names_of_cons_inv in Hy as [[-> ->] | Hy]
      | apply names_len_cons_inv in Hy as [[-> HT] | Hy]].
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
    + destruct (atom_len Γ ρ a T Hρ Ea HT) as (w & v0 & -> & Ew & Hw). rewrite Ev in Ew. injection Ew as ->.
      transitivity (vlength v0); [ | symmetry; apply vlen_lookup; cbn; now rewrite String.eqb_refl].
      cbn [subst_val vlen].
      replace (arr_image (bind_atom p T (AVar w) (inst_subst ps args)) p) with w; [apply vlen_lookup, Hw | ].
      destruct T; try discriminate HT; unfold arr_image; cbn; rewrite ?String.eqb_refl; reflexivity.
    + assert (y <> p) by (intros ->; apply Hp; eapply names_len_dom; exact Hy).
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
  unfold agree_ctx. rewrite !names_of_app, names_len_app. unfold res_subst.
  assert (Hne : forall y T', In y (names_of T' ps) -> y <> nu)
    by (intros y T' Hy ->; apply Hnu; eapply names_of_dom; exact Hy).
  assert (Hne' : forall y, In y (names_len ps) -> y <> nu)
    by (intros y Hy ->; apply Hnu; eapply names_len_dom; exact Hy).
  assert (Hx' : lookup x ((x, v) :: ρ) = Some v) by (cbn; now rewrite String.eqb_refl).
  split; [ | split]; intros y Hy; apply in_app_or in Hy as [Hy | Hy].
  - destruct (bind_atom_other nu T (AVar x) (inst_subst ps args) (val_of_env ((x, v) :: ρ)) y (Hne y _ Hy))
      as (-> & _ & _).
    rewrite (Ai y Hy). cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct v as [z| | | |]; try contradiction. cbn. rewrite ?String.eqb_refl. cbn. now rewrite ?String.eqb_refl.
  - destruct (bind_atom_other nu T (AVar x) (inst_subst ps args) (val_of_env ((x, v) :: ρ)) y (Hne y _ Hy))
      as (_ & -> & _).
    rewrite (Ab y Hy). cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne y _ Hy)).
  - apply names_of_cons_inv in Hy as [[-> ->] | []].
    destruct v as [|c| | |]; try contradiction. cbn. rewrite ?String.eqb_refl. cbn. now rewrite ?String.eqb_refl.
  - destruct (bind_atom_other nu T (AVar x) (inst_subst ps args) (val_of_env ((x, v) :: ρ)) y (Hne' y Hy))
      as (_ & _ & ->).
    rewrite (Al y Hy). cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne' y Hy)).
  - apply names_len_cons_inv in Hy as [[-> HT] | []].
    transitivity (vlength v); [ | symmetry; apply vlen_lookup; reflexivity].
    cbn [subst_val vlen].
    replace (arr_image (bind_atom nu T (AVar x) (inst_subst ps args)) nu) with x; [apply vlen_lookup, Hx' | ].
    destruct T; try discriminate HT; unfold arr_image; cbn; rewrite ?String.eqb_refl; reflexivity.
Qed.

(** The refinement of a result at [return a]. *)
Lemma ret_inst_hold : forall Γ ρ a T v ψ,
  env_ok ρ Γ -> atom_ty Γ a = Some T -> eval_atom ρ a = Some v -> ~ In nu (map fst Γ) ->
  scoped (Γ ++ [(nu, T)]) ψ ->
  hold ρ (ret_inst T a ψ) <-> hold ((nu, v) :: ρ) ψ.
Proof.
  intros Γ ρ a T v ψ Hρ Ha Hv Hnu Hp. unfold hold, ret_inst. rewrite holds_subst.
  apply (holds_agree_ctx (Γ ++ [(nu, T)]) _ _ ψ Hp).
  unfold agree_ctx. rewrite !names_of_app, names_len_app.
  assert (Hne : forall y T', In y (names_of T' Γ) -> y <> nu)
    by (intros y T' Hy ->; apply Hnu; eapply names_of_dom; exact Hy).
  assert (Hne' : forall y, In y (names_len Γ) -> y <> nu)
    by (intros y Hy ->; apply Hnu; eapply names_len_dom; exact Hy).
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
  - destruct (bind_atom_other nu T a subst_empty (val_of_env ρ) y (Hne' y Hy)) as (_ & _ & ->).
    cbn. unfold arr_image. cbn. now rewrite (proj2 (String.eqb_neq y nu) (Hne' y Hy)).
  - apply names_len_cons_inv in Hy as [[-> HT] | []].
    destruct (atom_len Γ ρ a T Hρ Ha HT) as (w & v0 & -> & Ew & Hw). rewrite Hv in Ew. injection Ew as <-.
    transitivity (vlength v); [ | symmetry; apply vlen_lookup; reflexivity].
    cbn [subst_val vlen].
    replace (arr_image (bind_atom nu T (AVar w) subst_empty) nu) with w; [apply vlen_lookup, Hw | ].
    destruct T; try discriminate HT; unfold arr_image; cbn; rewrite ?String.eqb_refl; reflexivity.
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

(** A hypothesis over lengths only, such as those of [match]. *)
Lemma len_hyp_scoped : forall Γ p, fvars p = [] -> fbvars p = [] -> kappas_ok [] p = true ->
  (forall a, In a (flens p) -> In a (names_len Γ)) -> scoped Γ p.
Proof.
  intros Γ p H1 H2 H3 H4. apply scoped_intro; [rewrite H1; intros y [] | rewrite H2; intros y [] | exact H4 | exact H3].
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

(** ** Scopes of contracts *)

Lemma pres_ok_scoped : forall seen ps pres, pres_ok [] seen ps pres = true -> Forall (scoped (seen ++ ps)) pres.
Proof.
  intros seen ps. revert seen. induction ps as [|p ps IH]; intros seen [|q pres] H; cbn in H; try discriminate H.
  - constructor.
  - apply andb_prop in H as [Hq H]. constructor.
    + apply (scoped_mono (seen ++ [p])); [ | exact Hq].
      intros r Hr. apply in_app_or in Hr as [Hr | [<- | []]]; apply in_or_app; [left; exact Hr | right; now left].
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
  match T, a with
  | TyArr, AVar w | TyList, AVar w => if String.eqb y p then w else arr_image σ y
  | _, _ => arr_image σ y
  end.
Proof. intros. destruct T, a; try reflexivity; unfold arr_image; cbn; destruct (String.eqb y p); reflexivity. Qed.

Lemma inst_scope : forall Γ ps args, atoms_ty Γ args = Some (map snd ps) ->
  (forall y, In y (names_of TyInt ps) -> exists t, assoc y (s_int (inst_subst ps args)) = Some t /\
                                                   incl (tvars t) (names_of TyInt Γ) /\ tlens t = []) /\
  (forall y, In y (names_of TyBool ps) -> exists b, assoc y (s_bool (inst_subst ps args)) = Some b /\
                                                    incl (bvars b) (names_of TyBool Γ)) /\
  (forall y, In y (names_len ps) -> In (arr_image (inst_subst ps args) y) (names_len Γ)).
Proof.
  intros Γ ps. induction ps as [|[p T] ps IH]; intros args Ha.
  - split; [ | split]; intros y [].
  - destruct args as [|a args]; [discriminate Ha | ]. cbn in Ha.
    destruct (atom_ty Γ a) as [U | ] eqn:Ea; [ | discriminate Ha].
    destruct (atoms_ty Γ args) as [Us | ] eqn:Eas; [ | discriminate Ha]. injection Ha as HU HUs. subst U Us.
    destruct (IH args Eas) as (IHi & IHb & IHa). cbn [inst_subst].
    split; [ | split]; intros y Hy; rewrite ?s_int_bind, ?s_bool_bind, ?arr_image_bind;
      [apply names_of_cons_inv in Hy as [[-> ->] | Hy] | apply names_of_cons_inv in Hy as [[-> ->] | Hy]
      | apply names_len_cons_inv in Hy as [[-> HT] | Hy]].
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
    + destruct T; try discriminate HT; destruct a; cbn in Ea; try discriminate Ea; rewrite String.eqb_refl;
        exact (lookup_names_len Γ _ _ Ea eq_refl).
    + specialize (IHa y Hy). destruct T, a; try exact IHa;
        destruct (String.eqb y p); first [exact (lookup_names_len Γ _ _ Ea eq_refl) | exact IHa].
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
  assert (Hself : forall U, In x (names_of U ((x, U) :: Γ))) by (intros U; apply names_of_iff; now left).
  unfold res_subst. split; [ | split]; cbn [sc_int sc_bool sc_arr scope_of]; intros y Hy;
    first [rewrite names_of_app in Hy | rewrite names_len_app in Hy]; apply in_app_or in Hy as [Hy | Hy].
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
  - specialize (Har y Hy). assert (Hyn : y <> nu) by (intros ->; apply Hnu; eapply names_len_dom; exact Hy).
    replace (arr_image (bind_atom nu T (AVar x) (inst_subst ps args)) y) with (arr_image (inst_subst ps args) y).
    + apply names_len_cons, Har.
    + rewrite arr_image_bind. destruct T; try reflexivity; rewrite (proj2 (String.eqb_neq y nu) Hyn); reflexivity.
  - apply names_len_cons_inv in Hy as [[-> HT] | []].
    replace (arr_image (bind_atom nu T (AVar x) (inst_subst ps args)) nu) with x.
    + exact (in_names_len ((x, T) :: Γ) x T (or_introl eq_refl) HT).
    + destruct T; try discriminate HT; unfold arr_image; cbn; rewrite ?String.eqb_refl; reflexivity.
Qed.
