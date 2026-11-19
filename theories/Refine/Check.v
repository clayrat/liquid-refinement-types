(** * Algorithm 1: checking the contracts

    - [check_fun] checks a body under the refinements of its parameters
      against the refinement of its result;
    - [check_prog] checks the base types of the program, the scopes and
      sorts of its contracts, and every function;
    - [check_client] checks an expression with free variables [Γ] under
      the hypotheses [φ] against the property [ψ] of its result.

    The answer is the complete list of obligations with the verdicts of
    the solver, which is a parameter [oracle]; a program is accepted
    when every verdict is [Proved].  Recursion needs no code of its own:
    the contract of a callee is taken from the table whatever body is
    being checked.

    The rule of calls is a parameter of the [_with] variants, for the
    second demonstration; [check_prog] and [check_client] use the main
    rule [RuleName], and only they enter the theorems. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing.
From Liquid.Refine Require Import Spec Wp Gen.

Local Open Scope string_scope.
Local Open Scope list_scope.

Record client : Type := mkClient {
  cl_env : tenv;            (** the free variables and their base types *)
  cl_pre : list formula;    (** φ, over the free variables *)
  cl_expr : expr;
  cl_post : formula         (** ψ, over the free variables and ν *)
}.

Definition fun_obligations (rule : call_rule) (P : prog) (S : spec) (fd : fundef) : list obligation :=
  let c := contract_of S fd in
  gen rule P S (fd_name fd) (fd_params fd) (pre_hyps c) (fd_body fd) (c_post c).

Definition prog_obligations (rule : call_rule) (P : prog) (S : spec) : list obligation :=
  flat_map (fun_obligations rule P S) P.

Definition client_scope : string := "client".

Definition client_obligations (rule : call_rule) (P : prog) (S : spec) (cl : client) : list obligation :=
  gen rule P S client_scope (cl_env cl) (fold_left extend (cl_pre cl) []) (cl_expr cl) (cl_post cl).

(** The scopes and sorts of a client against the signature [K]; its
    type. *)
Definition client_ok (K : ksig) (P : prog) (cl : client) : result string ty :=
  let* _ := require (distinct (map fst (cl_env cl)) && forallb (fun x => negb (reserved x)) (map fst (cl_env cl)))
                    "the variables of the client" in
  let* T := ty_expr P (cl_env cl) (cl_expr cl) in
  let* _ := require (forallb (formula_ok K (scope_of (cl_env cl))) (cl_pre cl)
                     && formula_ok K (scope_of (cl_env cl ++ [(nu, T)])) (cl_post cl))
                    "the refinements of the client: scope or sorts" in
  Ok T.

Section Check.
  Context {C : Type} (oracle : obligation -> verdict C).

  Definition judge (obs : list obligation) : list (obligation * verdict C) :=
    map (fun ob => (ob, oracle ob)) obs.

  Definition all_proved (r : list (obligation * verdict C)) : bool :=
    forallb (fun p => is_proved (snd p)) r.

  Definition check_fun (P : prog) (S : spec) (fd : fundef) : list (obligation * verdict C) :=
    judge (fun_obligations RuleName P S fd).

  Definition check_prog_with (rule : call_rule) (P : prog) (S : spec)
    : result string (list (obligation * verdict C)) :=
    let* _ := ty_prog P in
    let* _ := require (spec_ok [] P S) "the contracts: scope or sorts" in
    Ok (judge (prog_obligations rule P S)).

  Definition check_client_with (rule : call_rule) (P : prog) (S : spec) (cl : client)
    : result string (list (obligation * verdict C)) :=
    let* _ := ty_prog P in
    let* _ := require (spec_ok [] P S) "the contracts: scope or sorts" in
    let* _ := client_ok [] P cl in
    Ok (judge (client_obligations rule P S cl)).

  Definition check_prog := check_prog_with RuleName.
  Definition check_client := check_client_with RuleName.

  (** Accepted: checked, and every obligation proved. *)
  Definition accepted (r : result string (list (obligation * verdict C))) : bool :=
    match r with Ok l => all_proved l | Err _ => false end.
End Check.
