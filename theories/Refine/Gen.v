(** * The generator of obligations

    [gen φ e ψ] walks the program forward, accumulating the hypotheses
    [φ], and emits the flat obligations directly:

      return a:                  emit φ ⇒ ψ[a/ν]
      let r = op(ā) in e:        emit φ ⇒ Pre_op(ā),  go on under φ ∧ Post_op(ā, r)
      let r = f(ā) in e:         emit φ ⇒ Pre_f(ā),   go on under φ ∧ Post_f(ā, r)
      if c then e₁ else e₂:      gen(φ ∧ c, e₁, ψ) and gen(φ ∧ ¬c, e₂, ψ)
      match x with nil → e₁ | cons h t → e₂:
                                 gen(φ ∧ len x = 0, e₁, ψ) and gen(φ ∧ len x = 1 + len t, e₂, ψ)

    It uses the same contracts and sorted substitutions as [wp] of
    Refine/Wp.v, and the statement of the lecture "the generator unfolds
    [wp] as it walks" is a lemma on lists ([gen_flatten]): [gen φ e ψ]
    is [flatten φ (wp e ψ)], for either rule of calls.  An obligation
    whose goal is syntactically [true] is not emitted, by the same
    function [emit] as in [flatten]; otherwise every addition would add
    [φ ⊢ true] from [Pre_op = true]. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing.
From Liquid.Refine Require Import Spec Wp.

Local Open Scope string_scope.
Local Open Scope list_scope.

Section Gen.
  Variable rule : call_rule.
  Variable P : prog.
  Variable S : spec.
  Variable scope : string.

  Fixpoint gen (Γ : tenv) (φ : list formula) (e : expr) (ψ : formula) : list obligation :=
    match e with
    | ERet a => emit (LResult scope) φ (ret_inst (atom_type Γ a) a ψ)
    | EPrim x p args e' =>
        let c := prim_contract p in
        let T := snd (prim_sig p) in
        emit (LPre scope (prim_name p) x) φ (pre_inst c (prim_params p) args)
          ++ gen ((x, T) :: Γ) (extend φ (post_inst c (prim_params p) T args x)) e' ψ
    | ECall x f args e' =>
        match find_fun f P with
        | Some fd =>
            let c := contract_of S fd in
            emit (LPre scope f x) φ (pre_inst c (fd_params fd) args)
              ++ gen ((x, fd_ret fd) :: Γ) (extend φ (call_hyp rule c (fd_params fd) (fd_ret fd) args x)) e' ψ
        | None => emit (LPre scope f x) φ ffalse
        end
    | EIf c e1 e2 =>
        gen Γ (extend φ (cond_formula c)) e1 ψ ++ gen Γ (extend φ (FNot (cond_formula c))) e2 ψ
    | EMatch x e1 h t e2 =>
        gen Γ (extend φ (nil_hyp x)) e1 ψ ++ gen ((t, TyList) :: (h, TyInt) :: Γ) (extend φ (cons_hyp x t)) e2 ψ
    end.

  Theorem gen_flatten : forall Γ φ e ψ, gen Γ φ e ψ = flatten φ (wp rule P S scope Γ e ψ).
  Proof.
    intros Γ φ e. revert Γ φ.
    induction e as [a | x p args e IH | x f args e IH | c e1 IH1 e2 IH2 | x e1 IH1 h t e2 IH2];
      intros Γ φ ψ; cbn.
    - reflexivity.
    - now rewrite IH.
    - destruct (find_fun f P); [now rewrite IH | reflexivity].
    - now rewrite IH1, IH2.
    - now rewrite IH1, IH2.
  Qed.
End Gen.
