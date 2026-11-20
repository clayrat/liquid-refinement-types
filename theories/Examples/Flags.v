(** * Boolean refinements

      yes : {x:Int | 0 < x} → {ν:Bool | ν}
      yes x = if 0 < x then true else false

      choose : {b:Bool | b} → x:Int → {ν:Int | ν = x}
      choose b x = if b then x else 0

    Not an example of the lecture: the inputs of the tests of booleans
    (Tests.v, and the differential test of the native reference).

    For the solver a boolean variable [b] is a node of the graph with
    [0 ≤ b ≤ 1]; the atom [b] is the edge [1 ≤ b], and [¬b] is [b ≤ 0].
    The branch [else] of [choose] is dead under its precondition [b], so
    its postcondition [ν = x] holds; the branch [else] of [client_yes]
    is dead under the postcondition of [yes] for its result.  Without
    the precondition, the branch [else] of [choose] is refuted by a
    model with [b] false; [client_branch] by a model with [b] true.

    [flags_tspec] puts unknowns over booleans in place of the three
    refinements: the qualifiers [ν] and [¬ν] for the result of [yes],
    [b] and [¬b] for the flag of [choose], [0 ≤ ν], [ν = x] and [ν = 0]
    for its result.  Weakening keeps [ν], removes [¬b] by the call
    [choose true 5] of [client_choose], and then keeps [ν = x] only:
    the precondition is found from the client.  Without clients nothing
    calls [choose], its precondition stays the strongest, [b ∧ ¬b], and
    every qualifier of its result is kept. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From Liquid.Logic Require Import Formula.
From Liquid.Lang Require Import Syntax Typing Eval.
From Liquid.Refine Require Import Spec Check.
From Liquid.Liquid Require Import Template.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition bvar (b : string) : formula := FAtom (BVar b).

Definition yes_def : fundef :=
  mkFun "yes" [("x", TyInt)] TyBool (ifc CLt (num 0) "x" (ERet (ABool true)) (ERet (ABool false))).

Definition choose_def : fundef :=
  mkFun "choose" [("b", TyBool); ("x", TyInt)] TyInt (EIf (CAtom "b") (ERet "x") (ERet (num 0))).

Definition flags_prog : prog := [yes_def; choose_def].

Definition yes_contract : contract := mkContract [FLt (TConst 0) (TVar "x")] (bvar nu).
Definition choose_contract : contract := mkContract [bvar "b"; ftrue] (FEq (TVar nu) (TVar "x")).

Definition flags_spec : spec := [("yes", yes_contract); ("choose", choose_contract)].

(** [¬ν] for [yes]: refuted in the branch [then]. *)
Definition flags_spec_yes_wrong : spec :=
  [("yes", mkContract [FLt (TConst 0) (TVar "x")] (FNot (bvar nu))); ("choose", choose_contract)].

(** [choose] without its precondition: the branch [else] is refuted. *)
Definition flags_spec_no_flag : spec :=
  [("yes", yes_contract); ("choose", mkContract [ftrue; ftrue] (FEq (TVar nu) (TVar "x")))].

(** ** Clients *)

(** The result of [yes 1] is [true]: the branch [else] is dead. *)
Definition client_yes : client :=
  mkClient [] [] (lcall "b" "yes" [num 1] (EIf (CAtom "b") (ERet (num 1)) (ERet (num 0)))) (FEq (TVar nu) (TConst 1)).

(** [yes 0] violates the precondition. *)
Definition client_yes0 : client :=
  mkClient [] [] (lcall "b" "yes" [num 0] (ERet "b")) ftrue.

Definition client_choose : client :=
  mkClient [] [] (lcall "r" "choose" [ABool true; num 5] (ERet "r")) (FEq (TVar nu) (TConst 5)).

(** [choose false 5] violates the precondition. *)
Definition client_choose_false : client :=
  mkClient [] [] (lcall "r" "choose" [ABool false; num 5] (ERet "r")) ftrue.

(** A free boolean [b]: the branch [then] returns [0], refuted by [b]
    true. *)
Definition client_branch : client :=
  mkClient [("b", TyBool)] [] (EIf (CAtom "b") (ERet (num 0)) (ERet (num 1))) (FEq (TVar nu) (TConst 1)).

(** The same under the hypothesis [¬b]: the branch [then] is dead. *)
Definition client_branch_not : client :=
  mkClient [("b", TyBool)] [FNot (bvar "b")] (EIf (CAtom "b") (ERet (num 0)) (ERet (num 1))) (FEq (TVar nu) (TConst 1)).

(** ** Unknowns over booleans *)

Definition flags_tspec : tspec :=
  [("yes", mkCT [fixed (FLt (TConst 0) (TVar "x"))] (holed ftrue (mkHole "κy" [bvar nu; FNot (bvar nu)])));
   ("choose", mkCT [holed ftrue (mkHole "κb" [bvar "b"; FNot (bvar "b")]); fixed ftrue]
                   (holed ftrue (mkHole "κr" [FLe (TConst 0) (TVar nu); FEq (TVar nu) (TVar "x");
                                              FEq (TVar nu) (TConst 0)])))].
