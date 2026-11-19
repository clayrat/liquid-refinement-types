(** * [inc 0 = 1] through the name of the result

      inc : x:Int → {ν:Int | ν = x + 1}
      client = let r = inc 0 in r        required: ν = 1

    With the main rule of calls the hypothesis after the call is
    [Post_inc(0, r) = (r = 0 + 1)], and the client is accepted.  With
    the root rule [APPᶜ] of the paper it is [r = r.x + 1] for a fresh
    [r.x]: the link with the argument [0] is lost, and the solver
    refutes the obligation with a model. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Check.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition inc_contract : contract := mkContract [ftrue] (FEq (TVar nu) (TAdd (TVar "x") (TConst 1))).

Definition inc_spec : spec := [("inc", inc_contract)].

Definition inc_def : fundef := mkFun "inc" [("x", TyInt)] TyInt (ladd "y" "x" (num 1) (ERet "y")).

Definition inc_prog : prog := [inc_def].

Definition client_inc0 : client := mkClient [] [] (lcall "r" "inc" [num 0] (ERet "r")) (FEq (TVar nu) (TConst 1)).
