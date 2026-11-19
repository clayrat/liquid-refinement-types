(* The differential test: the native reference (liquid_native.ml) against
   the extract on every example of the lecture — the lists of
   obligations, the kinds of the verdicts (a counter-model of either side
   checked on the obligation by the other side), for inference the
   qualifiers removed, in order, the final assignment and the kind of the
   answer, and the obligations of the measures of termination.

   The native reference has its own syntax and does not see the extract.
   The bridge below translates the examples of the extract into the
   native syntax, constructor by constructor, and the counter-models in
   both directions; the results are compared in the native syntax.  The
   integers need no translation: the big integers of the extract are
   Zarith's. *)
open Liquid
module N = Liquid_native

(* ---- the bridge ---- *)

let rec n_term = function
  | TVar x -> N.TVar x
  | TConst z -> N.TConst z
  | TAdd (a, b) -> N.TAdd (n_term a, n_term b)
  | TSub (a, b) -> N.TSub (n_term a, n_term b)
  | TMul (k, t) -> N.TMul (k, n_term t)
  | TLen a -> N.TLen a

let n_batom = function BVar x -> N.BVar x | BConst c -> N.BConst c
let n_arg = function UInt t -> N.UInt (n_term t) | UBool b -> N.UBool (n_batom b)

let rec n_formula = function
  | FLe (a, b) -> N.FLe (n_term a, n_term b)
  | FLt (a, b) -> N.FLt (n_term a, n_term b)
  | FEq (a, b) -> N.FEq (n_term a, n_term b)
  | FAtom b -> N.FAtom (n_batom b)
  | FKappa (k, us) -> N.FKappa (k, List.map n_arg us)
  | FAnd (p, q) -> N.FAnd (n_formula p, n_formula q)
  | FOr (p, q) -> N.FOr (n_formula p, n_formula q)
  | FNot p -> N.FNot (n_formula p)

let n_label = function
  | LResult s -> N.LResult s
  | LPre (s, f, x) -> N.LPre (s, f, x)
  | LMeasureNonneg f -> N.LMeasureNonneg f
  | LMeasureDecr (f, x) -> N.LMeasureDecr (f, x)

let n_obligation (ob : obligation) : N.obligation =
  { N.ob_label = n_label ob.ob_label; ob_hyps = List.map n_formula ob.ob_hyps; ob_goal = n_formula ob.ob_goal }

let n_cmodel (m : cmodel) : N.cmodel = { N.cm_int = m.cm_int; cm_bool = m.cm_bool; cm_len = m.cm_len }
let x_cmodel (m : N.cmodel) : cmodel = { cm_int = m.N.cm_int; cm_bool = m.N.cm_bool; cm_len = m.N.cm_len }

let n_ty = function TyInt -> N.TyInt | TyBool -> N.TyBool | TyUnit -> N.TyUnit | TyArr -> N.TyArr
let n_atom = function AVar x -> N.AVar x | ANum z -> N.ANum z | ABool b -> N.ABool b | AUnit -> N.AUnit
let n_cmp = function CLt -> N.CLt | CLe -> N.CLe | CEq -> N.CEq
let n_cond = function CAtom a -> N.CAtom (n_atom a) | CCmp (c, a, b) -> N.CCmp (n_cmp c, n_atom a, n_atom b)
let n_prim = function PAdd -> N.PAdd | PSub -> N.PSub | PLength -> N.PLength | PGet -> N.PGet

let rec n_expr = function
  | ERet a -> N.ERet (n_atom a)
  | EPrim (x, p, args, e) -> N.EPrim (x, n_prim p, List.map n_atom args, n_expr e)
  | ECall (x, f, args, e) -> N.ECall (x, f, List.map n_atom args, n_expr e)
  | EIf (c, e1, e2) -> N.EIf (n_cond c, n_expr e1, n_expr e2)

let n_env g = List.map (fun (x, t) -> (x, n_ty t)) g

let n_fundef (fd : fundef) : N.fundef =
  { N.fd_name = fd.fd_name; fd_params = n_env fd.fd_params; fd_ret = n_ty fd.fd_ret; fd_body = n_expr fd.fd_body }

let n_prog p = List.map n_fundef p
let n_contract (c : contract) : N.contract = { N.c_pre = List.map n_formula c.c_pre; c_post = n_formula c.c_post }
let n_spec s = List.map (fun (f, c) -> (f, n_contract c)) s

let n_client (cl : client) : N.client =
  { N.cl_env = n_env cl.cl_env; cl_pre = List.map n_formula cl.cl_pre; cl_expr = n_expr cl.cl_expr;
    cl_post = n_formula cl.cl_post }

let n_hole (h : hole) : N.hole = { N.hl_name = h.hl_name; hl_quals = List.map n_formula h.hl_quals }
let n_rt (rt : rtemplate) : N.rtemplate = { N.rt_fixed = n_formula rt.rt_fixed; rt_hole = Option.map n_hole rt.rt_hole }
let n_ct (ct : ctemplate) : N.ctemplate = { N.ct_pre = List.map n_rt ct.ct_pre; ct_post = n_rt ct.ct_post }
let n_tspec t = List.map (fun (f, ct) -> (f, n_ct ct)) t
let n_measures m = List.map (fun (f, mu) -> (f, n_term mu)) m
let n_solution sol = List.map (fun (k, qs) -> (k, List.map n_formula qs)) sol

(* ---- the checks ---- *)

let failures = ref 0
let checks = ref 0

let check name b =
  incr checks;
  if not b then begin incr failures; Printf.printf "FAIL %s\n" name end

let kind_x = function Proved _ -> "Proved" | Refuted _ -> "Refuted" | Unknown _ -> "Unknown"
let kind_n = function N.NProved -> "Proved" | N.NRefuted _ -> "Refuted" | N.NUnknown _ -> "Unknown"

(* The obligations of the extract [xs] and the native ones [ns]: equal
   after translation; then each side decides its own, and each
   counter-model is checked by the other side. *)
let compare_obligations name xs ns =
  check (name ^ ": the obligations") (List.map n_obligation xs = ns);
  if List.length xs = List.length ns then
    List.iteri
      (fun i (ob, ob') ->
        let vx = prove ob and vn = N.prove ob' in
        let tag = Printf.sprintf "%s: obligation %d" name i in
        check (tag ^ ": verdict " ^ kind_x vx ^ " / " ^ kind_n vn) (kind_x vx = kind_n vn);
        (match vx with Refuted m -> check (tag ^ ": the extract's model, natively") (N.falsifies (n_cmodel m) ob') | _ -> ());
        match vn with
        | N.NRefuted m -> check (tag ^ ": the native model, by the extract") (check_counter (x_cmodel m) ob)
        | _ -> ())
      (List.combine xs ns)

let programs =
  [ ("bounded", bounded, bounded_spec); ("bounded3", bounded3, bounded_spec); ("inc", inc_prog, inc_spec);
    ("sum", sum_prog, sum_spec); ("sum_le", sum_prog_le, sum_spec); ("loop", loop_prog, loop_spec) ]

let clients =
  [ ("f 1 + 2", bounded, bounded_spec, client_f1); ("f 2", bounded, bounded_spec, client_f2);
    ("f 2 unused", bounded, bounded_spec, client_f2_dropped); ("inc 0", inc_prog, inc_spec, client_inc0);
    ("two calls", bounded, bounded_spec, client_twice); ("loop", loop_prog, loop_spec, client_loop) ]

let () =
  List.iter
    (fun (n, p, s) -> compare_obligations n (prog_obligations RuleName p s) (N.prog_obligations (n_prog p) (n_spec s)))
    programs;
  List.iter
    (fun (n, p, s, cl) ->
      compare_obligations n (client_obligations RuleName p s cl)
        (N.client_obligations (n_prog p) (n_spec s) (n_client cl)))
    clients

let removed_x log =
  List.concat_map
    (function WStep (_, k, rem, _) -> List.map (fun ((q, _), _) -> (k, n_formula q)) rem | WRound _ -> [])
    log

let () =
  List.iter
    (fun (n, p, qs) ->
      let log, ax = infer prove p (sum_tspec qs) [] in
      let rn, an = N.infer (n_prog p) (n_tspec (sum_tspec qs)) [] in
      check (n ^ ": the qualifiers removed") (removed_x log = rn);
      match ax, an with
      | Inferred (_, sol, _), N.NInferred sol' -> check (n ^ ": the assignment") (n_solution sol = sol')
      | IRefuted (ob, _), N.NRefusedAt (ob', _) -> check (n ^ ": the refused obligation") (n_obligation ob = ob')
      | IUndecided (ob, _), N.NUndecided ob' -> check (n ^ ": the undecided obligation") (n_obligation ob = ob')
      | _ -> check (n ^ ": the kinds of the answers") false)
    [ ("inference", sum_prog, quals); ("inference with ≤", sum_prog_le, quals);
      ("inference without 0 ≤ i", sum_prog, quals_no_lower) ]

(* Malformed templates: both sides refuse them, neither trims them. *)
let () =
  let inc_two_pres =
    { ct_pre = [ { rt_fixed = ftrue; rt_hole = None }; { rt_fixed = ffalse; rt_hole = None } ];
      ct_post = (of_contract inc_contract).ct_post }
  in
  List.iter
    (fun (n, p, t) ->
      let failed_x = match snd (infer prove p t []) with IFailed _ -> true | _ -> false in
      let failed_n = match snd (N.infer (n_prog p) (n_tspec t) []) with N.NFailed _ -> true | _ -> false in
      check (n ^ ": the extract refuses the templates") failed_x;
      check (n ^ ": the native reference refuses the templates") failed_n)
    [ ("a template for an unknown function", sum_prog, sum_tspec quals @ [ ("typo", of_contract inc_contract) ]);
      ("two refinements for one parameter", inc_prog, [ ("inc", inc_two_pres) ]);
      ("two templates for go", sum_prog, sum_tspec quals @ [ ("go", go_template quals_no_lower) ]) ]

(* Measures: the obligations and their verdicts; malformed measures are
   refused by both sides, not ignored. *)
let () =
  List.iter
    (fun (n, p, s, m) ->
      match N.measure_obligations (n_prog p) (n_spec s) (n_measures m) with
      | Ok ns -> compare_obligations n (measure_obligations p s m) ns
      | Error e -> check (n ^ ": refused natively: " ^ e) false)
    [ ("measure of go", sum_prog, sum_spec, sum_measures);
      ("measure of go under 0 ≤ i", sum_prog, sum_spec_lower, sum_measures);
      ("measure of go with ≤", sum_prog_le, sum_spec, sum_measures);
      ("measure n of go", sum_prog, sum_spec, [ ("go", TVar "n") ]);
      ("measure of loop", loop_prog, loop_spec, loop_measures) ];
  List.iter
    (fun (n, m) ->
      let refused_x = match check_measures prove sum_prog sum_spec m with Err _ -> true | Ok _ -> false in
      let refused_n =
        match N.measure_obligations (n_prog sum_prog) (n_spec sum_spec) (n_measures m) with
        | Error _ -> true
        | Ok _ -> false
      in
      check (n ^ ": the extract refuses the measures") refused_x;
      check (n ^ ": the native reference refuses the measures") refused_n)
    [ ("a measure of an unknown function", sum_measures @ [ ("typo", TVar "x") ]);
      ("two measures for go", sum_measures @ [ ("go", TVar "n") ]);
      ("a measure over a local", [ ("go", TSub (TVar "n", TVar "j")) ]);
      ("a measure over a foreign array", [ ("go", TSub (TLen "b", TVar "i")) ]) ]

let () =
  Printf.printf "native reference: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
