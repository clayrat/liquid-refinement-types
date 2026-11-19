(** * The weakest precondition relative to contracts

    The four equations of the plan of the lecture; a call is read by the
    contract of the callee, not by its body:

      wp(return a, ψ)                   = ψ[a/ν]
      wp(let r = op(a₁, …, aₖ) in e, ψ) = Pre_op(ā) ∧ ∀r. Post_op(ā, r) ⇒ wp(e, ψ)
      wp(let r = f(ā) in e, ψ)          = Pre_f(ā) ∧ ∀r. Post_f(ā, r) ⇒ wp(e, ψ)
      wp(if c then e₁ else e₂, ψ)       = (c ⇒ wp(e₁, ψ)) ∧ (¬c ⇒ wp(e₂, ψ))

    The values of [wp] are a small type of nested formulas with [∧],
    [p ⇒ w] and [∀r. w]; their leaves carry the label of the obligation
    they become.  The expression [get a i] does not enter the logic: the
    name of its result is bound by [∀] and described by the
    postcondition of [get].

    [flatten H w] unfolds such a formula into the list of flat
    obligations: a conjunction splits, [p ⇒ w] moves [p] into the
    hypotheses, [∀r] is dropped, the names of results being fresh, and a
    leaf whose goal is syntactically [true] gives no obligation.

    The rule of calls is a switch, for the second demonstration: with
    [RuleRoot] the hypothesis after a call is [Pre_f(x′) ∧ Post_f(x′, r)]
    with fresh [x′], as in the rule [APPᶜ] of the paper, and the link
    with the actual argument is lost.  Only [RuleName] enters the
    theorems of soundness. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing.
From Liquid.Refine Require Import Spec.

Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive call_rule : Type := RuleName | RuleRoot.

Inductive wpf : Type :=
| WGoal (l : label) (g : formula)
| WAnd (w1 w2 : wpf)
| WImp (h : formula) (w : wpf)
| WAll (x : string) (w : wpf).

(** The hypothesis after [let r = f(ā)]. *)
Definition call_hyp (rule : call_rule) (c : contract) (ps : tenv) (ret : ty) (args : list atom) (r : string)
  : formula :=
  match rule with
  | RuleName => post_inst c ps ret args r
  | RuleRoot =>
      let args' := map (fun p => AVar (r ++ "." ++ fst p)) ps in
      fand (pre_inst c ps args') (post_inst c ps ret args' r)
  end.

Section Wp.
  Variable rule : call_rule.
  Variable P : prog.
  Variable S : spec.
  Variable scope : string.

  Fixpoint wp (Γ : tenv) (e : expr) (ψ : formula) : wpf :=
    match e with
    | ERet a => WGoal (LResult scope) (ret_inst (atom_type Γ a) a ψ)
    | EPrim x p args e' =>
        let c := prim_contract p in
        let T := snd (prim_sig p) in
        WAnd (WGoal (LPre scope (prim_name p) x) (pre_inst c (prim_params p) args))
             (WAll x (WImp (post_inst c (prim_params p) T args x) (wp ((x, T) :: Γ) e' ψ)))
    | ECall x f args e' =>
        match find_fun f P with
        | Some fd =>
            let c := contract_of S fd in
            WAnd (WGoal (LPre scope f x) (pre_inst c (fd_params fd) args))
                 (WAll x (WImp (call_hyp rule c (fd_params fd) (fd_ret fd) args x)
                               (wp ((x, fd_ret fd) :: Γ) e' ψ)))
        | None => WGoal (LPre scope f x) ffalse
        end
    | EIf c e1 e2 =>
        WAnd (WImp (cond_formula c) (wp Γ e1 ψ)) (WImp (FNot (cond_formula c)) (wp Γ e2 ψ))
    end.
End Wp.

Definition emit (l : label) (H : list formula) (g : formula) : list obligation :=
  if is_ftrue g then [] else [mkOb l H g].

Fixpoint flatten (H : list formula) (w : wpf) : list obligation :=
  match w with
  | WGoal l g => emit l H g
  | WAnd w1 w2 => flatten H w1 ++ flatten H w2
  | WImp h w => flatten (extend H h) w
  | WAll _ w => flatten H w
  end.
