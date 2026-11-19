(** * The evaluator with fuel

    [evalFuel k P ρ e] evaluates [e] by value, big step, in the
    environment [ρ] and the program [P], and answers

    - [Value v]: the evaluation finished with [v];
    - [Timeout]: the fuel ran out;
    - [Stuck why]: a partial primitive failed.

    Fuel decreases at every node, which is enough for an induction on
    one [k]; a call runs the body with the fuel left, and its
    continuation too.  The only primitive that gets stuck on well-typed
    arguments is [get] out of bounds, and its reason names the array,
    the index and the length.  The other reasons are failures of typing
    (an unbound variable, a wrong arity, an argument of the wrong type);
    Lang/EvalFacts.v shows that they do not happen in typed programs.

    The violation of a declared precondition of a user function does not
    stop the evaluation: the evaluator does not see the contracts, which
    are not in [prog]. *)

From Stdlib Require Import String List Bool ZArith Lia.
Import ListNotations.
From Liquid.Common Require Import Result.
From Liquid.Lang Require Import Syntax.

Local Open Scope Z_scope.

Inductive value : Type :=
| VInt (z : Z)
| VBool (b : bool)
| VUnit
| VArr (l : list Z).

Inductive stuck : Type :=
| SBounds (arr : list Z) (i : Z) (len : Z)
| SType (what : string).

Inductive answer : Type :=
| Value (v : value)
| Timeout
| Stuck (why : stuck).

Definition env : Type := list (string * value).

Fixpoint lookup {A} (x : string) (l : list (string * A)) : option A :=
  match l with
  | [] => None
  | (y, a) :: l' => if String.eqb x y then Some a else lookup x l'
  end.

Definition eval_atom (ρ : env) (a : atom) : option value :=
  match a with
  | AVar x => lookup x ρ
  | ANum z => Some (VInt z)
  | ABool b => Some (VBool b)
  | AUnit => Some VUnit
  end.

Fixpoint eval_atoms (ρ : env) (args : list atom) : option (list value) :=
  match args with
  | [] => Some []
  | a :: args' =>
      match eval_atom ρ a, eval_atoms ρ args' with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Definition get_at (l : list Z) (i : Z) : result stuck value :=
  if (0 <=? i) && (i <? Z.of_nat (List.length l))
  then Ok (VInt (nth (Z.to_nat i) l 0))
  else Err (SBounds l i (Z.of_nat (List.length l))).

Definition eval_prim (p : prim) (vs : list value) : result stuck value :=
  match p, vs with
  | PAdd, [VInt a; VInt b] => Ok (VInt (a + b))
  | PSub, [VInt a; VInt b] => Ok (VInt (a - b))
  | PLength, [VArr l] => Ok (VInt (Z.of_nat (List.length l)))
  | PGet, [VArr l; VInt i] => get_at l i
  | _, _ => Err (SType (prim_name p))
  end.

Definition eval_cmp (c : cmp) (a b : Z) : bool :=
  match c with
  | CLt => a <? b
  | CLe => a <=? b
  | CEq => a =? b
  end.

Definition eval_cond (ρ : env) (c : cond) : option bool :=
  match c with
  | CAtom a => match eval_atom ρ a with Some (VBool b) => Some b | _ => None end
  | CCmp c a1 a2 =>
      match eval_atom ρ a1, eval_atom ρ a2 with
      | Some (VInt z1), Some (VInt z2) => Some (eval_cmp c z1 z2)
      | _, _ => None
      end
  end.

(** The environment of a body: the parameters bound to the arguments. *)
Fixpoint bind_params (ps : list (string * ty)) (vs : list value) : option env :=
  match ps, vs with
  | [], [] => Some []
  | (x, _) :: ps', v :: vs' =>
      match bind_params ps' vs' with Some ρ => Some ((x, v) :: ρ) | None => None end
  | _, _ => None
  end.

Fixpoint evalFuel (k : nat) (P : prog) (ρ : env) (e : expr) : answer :=
  match k with
  | O => Timeout
  | S k' =>
      match e with
      | ERet a =>
          match eval_atom ρ a with
          | Some v => Value v
          | None => Stuck (SType "unbound variable")
          end
      | EPrim x p args e' =>
          match eval_atoms ρ args with
          | Some vs =>
              match eval_prim p vs with
              | Ok v => evalFuel k' P ((x, v) :: ρ) e'
              | Err why => Stuck why
              end
          | None => Stuck (SType "unbound variable")
          end
      | ECall x f args e' =>
          match find_fun f P, eval_atoms ρ args with
          | Some fd, Some vs =>
              match bind_params (fd_params fd) vs with
              | Some ρf =>
                  match evalFuel k' P ρf (fd_body fd) with
                  | Value v => evalFuel k' P ((x, v) :: ρ) e'
                  | Timeout => Timeout
                  | Stuck why => Stuck why
                  end
              | None => Stuck (SType "arity")
              end
          | None, _ => Stuck (SType "unknown function")
          | _, None => Stuck (SType "unbound variable")
          end
      | EIf c e1 e2 =>
          match eval_cond ρ c with
          | Some true => evalFuel k' P ρ e1
          | Some false => evalFuel k' P ρ e2
          | None => Stuck (SType "condition")
          end
      end
  end.

(** A run of a function on arguments. *)
Definition run_fun (k : nat) (P : prog) (f : string) (vs : list value) : answer :=
  match find_fun f P with
  | Some fd =>
      match bind_params (fd_params fd) vs with
      | Some ρ => evalFuel k P ρ (fd_body fd)
      | None => Stuck (SType "arity")
      end
  | None => Stuck (SType "unknown function")
  end.

Definition diverges (P : prog) (ρ : env) (e : expr) : Prop := forall k, evalFuel k P ρ e = Timeout.
