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

    The environments as valuations of formulas, the scopes and the
    substitution of the formal parameters are in Refine/Env.v; this file
    follows the evaluator, one construct at a time.  The primitives have
    their own lemma, [prim_spec_sound]: the contracts of the primitives
    agree with their semantics: on typed arguments the precondition
    excludes [Stuck], and the result satisfies the postcondition; for
    [nil] and [cons] these are the equations of the measure [len].

    A [match] adds [len x = 0] or [len x = 1 + len t] in its branches; the
    head and the tail are fresh names, bound like the results of [let]. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing EvalFacts.
From Liquid.Refine Require Import Spec Wp Gen Check Env.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ** Answers

    [Timeout] is allowed, [Stuck] is not, and a value satisfies [ψ] with
    [ν] bound to it. *)

Definition answer_ok (a : answer) (ρ : env) (ψ : formula) : Prop :=
  match a with
  | Timeout => True
  | Value v => hold ((nu, v) :: ρ) ψ
  | Stuck _ => False
  end.

Lemma answer_ok_fresh : forall Γ ρ x v T ψ a,
  lookup x Γ = None -> x <> nu -> scoped (Γ ++ [(nu, T)]) ψ ->
  answer_ok a ((x, v) :: ρ) ψ -> answer_ok a ρ ψ.
Proof.
  intros Γ ρ x v T ψ a Hx Hn Hψ H. destruct a as [w | | ]; cbn in *; auto.
  exact (proj1 (hold_fresh_nu Γ ρ x v w T ψ Hx Hn Hψ) H).
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
  - eexists. split; [reflexivity | split; [exact I | ]]. unfold hold. reflexivity.
  - exists (VList (z :: l)). split; [reflexivity | split; [exact I | ]].
    change (Z.of_nat (S (length l)) = 1 + Z.of_nat (length l)). lia.
Qed.

(** ** The induction on fuel *)

Lemma emit_hold : forall l φ g ρ, (forall ob, In ob (emit l φ g) -> valid ob) -> Forall (hold ρ) φ -> hold ρ g.
Proof.
  intros l φ g ρ Hv Hφ. unfold emit in Hv. destruct (is_ftrue g) eqn:E; [apply is_ftrue_holds, E | ].
  exact (Hv _ (or_introl eq_refl) no_kappa (val_of_env ρ) (val_of_env_lens ρ) Hφ).
Qed.

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
    eapply He; [exact Ht | apply env_ok_cons; [ | exact Hv] | | | | exact Hval | ].
    - exact Hρ.
    - apply not_in_cons. split; [apply not_eq_sym, Hxn | exact Hnu].
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
    destruct e as [a | x p args e' | x f args e' | c e1 e2 | x e1 h t e2]; cbn [evalFuel]; cbn in Ht.
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
        * apply extend_Forall; [exact Hφs | intros _]. exact (cond_scoped Γ c H1 : scoped Γ (FNot (cond_formula c))).
        * intros ob H. apply Hv, in_or_app. now right.
        * apply extend_Forall; [exact Hφ | intros _]. intros H. apply Hc in H. discriminate H.
    - bind_in Ht u1 H1. bind_in Ht u2 H2. bind_in Ht u3 H3. bind_in Ht T1 HT1. bind_in Ht T2 HT2.
      bind_in Ht u4 H4. injection Ht as <-.
      apply require_ok in H1. destruct (lookup x Γ) as [[] | ] eqn:Ex; try discriminate H1.
      apply require_ok, fresh_ok_inv in H2 as [Hh Hhn]. apply require_ok, fresh_ok_inv in H3 as [Htt Htn].
      apply require_ok, ty_eqb_eq in H4. subst T2.
      destruct (Hρ x TyList Ex) as (v & Ev & Hvt). rewrite Ev.
      destruct v as [| | | | l]; try contradiction.
      cbn [gen] in Hv.
      assert (Hxl : In x (names_len Γ)) by exact (lookup_names_len Γ x TyList Ex eq_refl).
      destruct l as [|z l].
      + eapply He with (scope := scope) (φ := extend φ (nil_hyp x));
          [exact HT1 | exact Hρ | exact Hnu | | exact Hψs | | ].
        * apply extend_Forall; [exact Hφs | intros _].
          apply len_hyp_scoped; [reflexivity | reflexivity | reflexivity | ].
          intros a Ha. cbn in Ha. destruct Ha as [E | []]. subst a. exact Hxl.
        * intros ob H. apply Hv, in_or_app. now left.
        * apply extend_Forall; [exact Hφ | intros _]. unfold hold. cbn [holds teval nil_hyp].
          rewrite (vlen_lookup ρ x _ Ev). reflexivity.
      + assert (Hxh : x <> h) by (intros ->; rewrite Hh in Ex; discriminate Ex).
        assert (Hxt : x <> t).
        { intros E. subst t. rewrite (lookup_cons_neq h x TyInt Γ Hxh) in Htt. congruence. }
        apply (answer_ok_fresh Γ ρ h (VInt z) _ ψ _ Hh Hhn Hψs).
        apply (answer_ok_fresh ((h, TyInt) :: Γ) ((h, VInt z) :: ρ) t (VList l) _ ψ _ Htt Htn
                 (scoped_cons_nu _ _ _ _ _ Hψs)).
        eapply He with (scope := scope) (φ := extend φ (cons_hyp x t)); [exact HT2 | | | | | | ].
        * apply env_ok_cons; [apply env_ok_cons; [exact Hρ | exact I] | exact I].
        * apply not_in_cons. split; [apply not_eq_sym, Htn | ].
          apply not_in_cons. split; [apply not_eq_sym, Hhn | exact Hnu].
        * apply extend_Forall.
          -- eapply Forall_impl; [ | exact Hφs]. intros q Hq. apply scoped_cons, scoped_cons, Hq.
          -- intros _. apply len_hyp_scoped; [reflexivity | reflexivity | reflexivity | ].
             intros a Ha. cbn in Ha. destruct Ha as [E | [E | []]]; subst a.
             ++ apply names_len_cons, names_len_cons, Hxl.
             ++ exact (in_names_len ((t, TyList) :: (h, TyInt) :: Γ) t TyList (or_introl eq_refl) eq_refl).
        * apply scoped_cons_nu, scoped_cons_nu, Hψs.
        * intros ob H. apply Hv, in_or_app. now right.
        * apply extend_Forall.
          -- apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) Hφs q Hq) as Hqs.
             apply (proj2 (hold_fresh ((h, TyInt) :: Γ) ((h, VInt z) :: ρ) t (VList l) q Htt (scoped_cons _ _ _ _ Hqs))).
             apply (proj2 (hold_fresh Γ ρ h (VInt z) q Hh Hqs)).
             exact (proj1 (Forall_forall _ _) Hφ q Hq).
          -- intros _.
             assert (Lx : lookup x ((t, VList l) :: (h, VInt z) :: ρ) = Some (VList (z :: l))).
             { rewrite lookup_cons_neq by exact Hxt. rewrite lookup_cons_neq by exact Hxh. exact Ev. }
             assert (Lt : lookup t ((t, VList l) :: (h, VInt z) :: ρ) = Some (VList l))
               by (cbn; now rewrite String.eqb_refl).
             unfold hold. cbn [holds teval cons_hyp].
             rewrite (vlen_lookup _ x _ Lx), (vlen_lookup _ t _ Lt).
             change (Z.of_nat (S (length l)) = 1 + Z.of_nat (length l)). lia.
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
