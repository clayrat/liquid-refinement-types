(** * Algorithm 2: Liquid inference

    templates → [gen] for the definitions of the functions and, if given
    separately, for the client under [φ] against [ψ] → [normalize] and
    the check of shape → [weaken] → the solution substituted into the
    contracts → [check_prog] and, for a separate client, [check_client]
    again, with the same [φ] and [ψ].

    [Inferred] is returned only after every original obligation is
    proved again by the first algorithm ([infer_checked], by
    construction).  Checking the bodies alone does not establish that the
    calls of a client are allowed, hence the client in the recheck; a
    client written as a definition with its contract is covered by
    [check_prog].  The operational guarantee of the first algorithm
    applies to the result without any theorem about weakening: the
    inference is not in the trusted base.

    The obligations of the client come first, then those of the
    definitions in the order of the program: the order in which
    weakening meets them.

    Otherwise the answer is a refutation, with the obligation and the
    counter-model; [Undecided], with the obligation the solver did not
    decide; or a failure of the input (templates, types, scopes, shape).  The trace
    of weakening is returned with every answer. *)

From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
From Liquid.Common Require Import Result Traced.
From Liquid.Logic Require Import Formula Subst Obligation.
From Liquid.Lang Require Import Syntax Eval Typing.
From Liquid.Refine Require Import Spec Wp Gen Check.
From Liquid.Liquid Require Import Horn Weaken Template.

Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive ianswer (C : Type) : Type :=
| Inferred (S : spec) (sol : solution) (report : list (obligation * verdict C))
| IRefuted (ob : obligation) (m : cmodel)
| IUndecided (ob : obligation) (why : string)
| IFailed (why : string).

Arguments Inferred {C} _ _ _.
Arguments IRefuted {C} _ _.
Arguments IUndecided {C} _ _.
Arguments IFailed {C} _.

Section Infer.
  Context {C : Type} (oracle : obligation -> verdict C).

  (** The client with its refinements over the unknowns substituted. *)
  Definition apply_client (D : list kdecl) (sol : solution) (cl : client) : client :=
    mkClient (cl_env cl) (map (apply_sol D sol) (cl_pre cl)) (cl_expr cl) (apply_sol D sol (cl_post cl)).

  Definition clients_ok (K : ksig) (P : prog) (cls : list client) : result string unit :=
    let* _ := mapM (client_ok K P) cls in Ok tt.

  (** The recheck by the first algorithm. *)
  Definition recheck (P : prog) (S : spec) (cls : list client) : result string (list (obligation * verdict C)) :=
    let* r := check_prog oracle P S in
    let* rs := mapM (check_client oracle P S) cls in
    Ok (r ++ concat rs).

  Definition infer_obligations (P : prog) (S : spec) (cls : list client) : list obligation :=
    flat_map (client_obligations RuleName P S) cls ++ prog_obligations RuleName P S.

  Definition infer (P : prog) (T : tspec) (cls : list client) : list wevent * ianswer C :=
    match instantiate P T with
    | Err why => ([], IFailed why)
    | Ok (Sk, D) =>
    let K := ksig_of D in
    let checks :=
      let* _ := ty_prog P in
      let* _ := require (kdecls_ok D) "the qualifiers: scope or sorts" in
      let* _ := require (spec_ok K P Sk) "the templates: scope or sorts" in
      let* _ := clients_ok K P cls in
      horn_of (infer_obligations P Sk cls) in
    match checks with
    | Err why => ([], IFailed why)
    | Ok hs =>
        let (log, r) := run_traced (weaken oracle D hs) in
        match r with
        | Err (WRefuted ob m) => (log, IRefuted ob m)
        | Err (WUndecided ob why) => (log, IUndecided ob why)
        | Err (WUnknownKappa k) => (log, IFailed ("an unknown without qualifiers: " ++ k))
        | Err WOutOfFuel => (log, IFailed "out of fuel")
        | Ok sol =>
            let S' := apply_spec D sol Sk in
            let cls' := map (apply_client D sol) cls in
            match recheck P S' cls' with
            | Ok rep => if all_proved rep then (log, Inferred S' sol rep)
                        else (log, IFailed "the recheck by the first algorithm failed")
            | Err why => (log, IFailed why)
            end
        end
    end
    end.

  (** By construction, an inferred answer is accepted by the first
      algorithm, for the definitions and for every client. *)
  Theorem infer_checked : forall P T cls log S' sol rep,
    infer P T cls = (log, Inferred S' sol rep) ->
    exists D S,
      instantiate P T = Ok (S, D) /\ S' = apply_spec D sol S /\
      accepted (check_prog oracle P S') = true /\
      Forall (fun cl => accepted (check_client oracle P S' cl) = true) (map (apply_client D sol) cls).
  Proof.
    intros P T cls log S' sol rep H. unfold infer in H.
    destruct (instantiate P T) as [[S D] | why0] eqn:Ei; [ | discriminate H].
    destruct (let* _ := ty_prog P in _) as [hs | why]; [ | discriminate H].
    destruct (run_traced (weaken oracle D hs)) as [log1 [sol1 | e]].
    2: { destruct e; discriminate H. }
    destruct (recheck P (apply_spec D sol1 S) (map (apply_client D sol1) cls)) as [rep1 | why] eqn:Er;
      [ | discriminate H].
    destruct (all_proved rep1) eqn:Ea; [ | discriminate H].
    injection H as _ <- <- <-.
    exists D, S. split; [reflexivity | split; [reflexivity | ]].
    unfold recheck in Er. bind_in Er r1 Hr1. bind_in Er rs Hrs. injection Er as <-.
    unfold all_proved in Ea. rewrite forallb_app in Ea. apply andb_prop in Ea as [Ea1 Ea2].
    split.
    - unfold accepted. rewrite Hr1. exact Ea1.
    - apply mapM_ok in Hrs.
      assert (Hgen : forall l rs', Forall2 (fun a b => check_client oracle P (apply_spec D sol1 S) a = Ok b) l rs' ->
                forallb (fun p => is_proved (snd p)) (concat rs') = true ->
                Forall (fun cl => accepted (check_client oracle P (apply_spec D sol1 S) cl) = true) l).
      { intros l rs' Hl. induction Hl as [|a b l' rs'' Hab _ IH]; intros Hc; constructor.
        - unfold accepted. rewrite Hab. cbn in Hc. rewrite forallb_app in Hc. now apply andb_prop in Hc as [Hc _].
        - apply IH. cbn in Hc. rewrite forallb_app in Hc. now apply andb_prop in Hc as [_ Hc]. }
      exact (Hgen _ _ Hrs Ea2).
  Qed.
End Infer.
