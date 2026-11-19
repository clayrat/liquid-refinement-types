(* Printers for the extract: types, programs with contracts, formulas,
   nested wp formulas and flat obligations, verdicts with their
   certificates (a cycle of edges or a valuation), the trace of
   weakening and the answers of the evaluator.  Integers are Zarith's
   exact integers throughout. *)
open Liquid

let zs = Big_int_Z.string_of_big_int
let zi = Big_int_Z.big_int_of_int
let zero = Big_int_Z.zero_big_int
let is_zero z = Big_int_Z.sign_big_int z = 0
let is_neg z = Big_int_Z.sign_big_int z < 0
let zneg = Big_int_Z.minus_big_int

(* ---- base types and programs ---- *)

let ty = function TyInt -> "Int" | TyBool -> "Bool" | TyUnit -> "Unit" | TyArr -> "Array Int"

let atom = function
  | AVar x -> x
  | ANum z -> if is_neg z then "(" ^ zs z ^ ")" else zs z
  | ABool b -> string_of_bool b
  | AUnit -> "()"

let cmp = function CLt -> "<" | CLe -> "≤" | CEq -> "="

let cond = function
  | CAtom a -> atom a
  | CCmp (c, a1, a2) -> atom a1 ^ " " ^ cmp c ^ " " ^ atom a2

let prim_app p args =
  match p, args with
  | PAdd, [ a; b ] -> atom a ^ " + " ^ atom b
  | PSub, [ a; b ] -> atom a ^ " - " ^ atom b
  | PLength, [ a ] -> "length " ^ atom a
  | PGet, [ a; i ] -> "get " ^ atom a ^ " " ^ atom i
  | _ -> prim_name p ^ "(" ^ String.concat ", " (List.map atom args) ^ ")"

let call_app f args = String.concat " " (f :: List.map atom args)

let rec expr ind e =
  let pad = String.make ind ' ' in
  match e with
  | ERet a -> pad ^ atom a
  | EPrim (x, p, args, e') -> pad ^ "let " ^ x ^ " = " ^ prim_app p args ^ " in\n" ^ expr ind e'
  | ECall (x, f, args, e') -> pad ^ "let " ^ x ^ " = " ^ call_app f args ^ " in\n" ^ expr ind e'
  | EIf (c, e1, e2) ->
      pad ^ "if " ^ cond c ^ " then\n" ^ expr (ind + 2) e1 ^ "\n" ^ pad ^ "else\n" ^ expr (ind + 2) e2

(* ---- the logic ---- *)

let node = function NZero -> "0" | NInt x -> x | NBool b -> b | NLen a -> "len " ^ a

(* Terms by precedence: 0 sums, 1 products, 2 atoms. *)
let rec term_p prec t =
  let par p s = if prec > p then "(" ^ s ^ ")" else s in
  match t with
  | TVar x -> x
  | TConst z -> if is_neg z then "(" ^ zs z ^ ")" else zs z
  | TLen a -> "len " ^ a
  | TAdd (t1, t2) -> par 0 (term_p 0 t1 ^ " + " ^ term_p 1 t2)
  | TSub (t1, t2) -> par 0 (term_p 0 t1 ^ " - " ^ term_p 1 t2)
  | TMul (k, t) -> par 1 (zs k ^ "·" ^ term_p 2 t)

let term = term_p 0

let batom = function BVar b -> b | BConst c -> string_of_bool c
let arg = function UInt t -> term t | UBool b -> batom b

(* Formulas by precedence: 0 ∨, 1 ∧, 2 ¬ and atoms. *)
let rec formula_p prec p =
  let par q s = if prec > q then "(" ^ s ^ ")" else s in
  match p with
  | FLe (t1, t2) -> term t1 ^ " ≤ " ^ term t2
  | FLt (t1, t2) -> term t1 ^ " < " ^ term t2
  | FEq (t1, t2) -> term t1 ^ " = " ^ term t2
  | FAtom b -> batom b
  | FKappa (k, us) -> k ^ "(" ^ String.concat ", " (List.map arg us) ^ ")"
  | FAnd (p, q) -> par 1 (formula_p 1 p ^ " ∧ " ^ formula_p 1 q)
  | FOr (p, q) -> par 0 (formula_p 0 p ^ " ∨ " ^ formula_p 0 q)
  | FNot p -> "¬" ^ formula_p 3 p

let formula = formula_p 0

(* A refinement: a bare formula, or [true] printed as nothing. *)
let refinement x t p = if is_ftrue p then x ^ ":" ^ ty t else "{" ^ x ^ ":" ^ ty t ^ " | " ^ formula p ^ "}"

let contract_sig (fd : fundef) (c : contract) =
  let params = List.map2 (fun (x, t) p -> refinement x t p) fd.fd_params c.c_pre in
  String.concat " → " (params @ [ refinement nu fd.fd_ret c.c_post ])

let fundef_with (s : spec) (fd : fundef) =
  let c = contract_of s fd in
  fd.fd_name ^ " : " ^ contract_sig fd c ^ "\n"
  ^ fd.fd_name ^ " " ^ String.concat " " (List.map fst fd.fd_params) ^ " =\n"
  ^ expr 2 fd.fd_body

let program (p : prog) (s : spec) = String.concat "\n\n" (List.map (fundef_with s) p)

let label = function
  | LResult s -> "result of " ^ s
  | LPre (s, callee, x) -> "pre of " ^ callee ^ " at " ^ x ^ " in " ^ s
  | LMeasureNonneg s -> "measure of " ^ s ^ " non-negative"
  | LMeasureDecr (s, x) -> "measure of " ^ s ^ " decreases at " ^ x

let obligation (ob : obligation) =
  let hyps = match ob.ob_hyps with [] -> "" | hs -> String.concat ", " (List.map formula hs) ^ " " in
  hyps ^ "⊢ " ^ formula ob.ob_goal

(* ---- certificates and counter-models ---- *)

let edge ((a, w), b) =
  let lhs =
    match a with
    | NZero -> zs w
    | _ -> if is_zero w then node a else if is_neg w then node a ^ " - " ^ zs (zneg w) else node a ^ " + " ^ zs w
  in
  lhs ^ " ≤ " ^ node b

let cycle c = "[" ^ String.concat "; " (List.map edge c) ^ "]"

let cert_item = function
  | CertTrivial -> "true"
  | CertCycle (None, c) -> "hypotheses contradictory: " ^ cycle c
  | CertCycle (Some e, c) -> edge e ^ " by the cycle " ^ cycle c

let cmodel (m : cmodel) =
  let ints = List.map (fun (x, z) -> x ^ " = " ^ zs z) m.cm_int in
  let bools = List.map (fun (b, c) -> b ^ " = " ^ string_of_bool c) m.cm_bool in
  let lens = List.map (fun (a, z) -> "len " ^ a ^ " = " ^ zs z) m.cm_len in
  match ints @ bools @ lens with [] -> "any valuation" | l -> String.concat ", " l

let verdict_short = function
  | Proved _ -> "Proved"
  | Refuted m -> "Refuted: " ^ cmodel m
  | Unknown why -> "Unknown: " ^ why

let verdict ind = function
  | Proved c ->
      "Proved" ^ String.concat "" (List.map (fun ci -> "\n" ^ String.make ind ' ' ^ cert_item ci) c)
  | v -> verdict_short v

(* ---- wp ---- *)

let rec wpf ind w =
  let pad = String.make ind ' ' in
  match w with
  | WGoal (_, g) -> pad ^ formula g
  | WAnd (w1, w2) -> wpf ind w1 ^ "\n" ^ pad ^ "∧\n" ^ wpf ind w2
  | WImp (h, w) -> pad ^ formula h ^ " ⇒\n" ^ wpf (ind + 2) w
  | WAll (x, w) -> pad ^ "∀" ^ x ^ ".\n" ^ wpf (ind + 2) w

(* ---- weakening ---- *)

let qualifiers qs = match qs with [] -> "true" | _ -> String.concat ", " (List.map formula qs)

let wevent = function
  | WRound n -> "round " ^ zs n
  | WStep (l, k, removed, kept) ->
      let why =
        match removed with
        | [] -> "nothing removed"
        | _ ->
            String.concat "; "
              (List.map (fun ((q, _), m) -> "removed " ^ formula q ^ " (counter-model " ^ cmodel m ^ ")") removed)
      in
      "  " ^ label l ^ " ⊢ " ^ k ^ ": " ^ qualifiers kept ^ "\n    " ^ why

let solution (s : solution) = String.concat "; " (List.map (fun (k, qs) -> k ^ " := " ^ qualifiers qs) s)

(* ---- the evaluator ---- *)

let value = function
  | VInt z -> zs z
  | VBool b -> string_of_bool b
  | VUnit -> "()"
  | VArr l -> "[" ^ String.concat "; " (List.map zs l) ^ "]"

let answer = function
  | Value v -> "Value " ^ value v
  | Timeout -> "Timeout"
  | Stuck (SBounds (l, i, n)) -> "Stuck: get " ^ value (VArr l) ^ " " ^ zs i ^ " out of bounds (length " ^ zs n ^ ")"
  | Stuck (SType what) -> "Stuck: " ^ what
