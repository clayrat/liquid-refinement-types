(* The demonstrations of the lecture, from the extract.  Each prints into a
   buffer; main.ml prints them (make demo), regress.ml compares them with
   lecture9.expected. *)
open Liquid
open Pretty

let bprintf = Printf.bprintf
let fuel = zi 1000

let header b title = bprintf b "\n=== %s ===\n" title
let section b s = bprintf b "\n-- %s\n" s

let report b r =
  match r with
  | Err e -> bprintf b "  error: %s\n" e
  | Ok l ->
      List.iter
        (fun ((ob : obligation), v) ->
          bprintf b "  [%s]\n    %s\n    %s\n" (label ob.ob_label) (obligation ob) (verdict 6 v))
        l;
      bprintf b "  => %s\n" (if all_proved l then "accepted" else "rejected")

(* One line per obligation: the label and the verdict without its certificate. *)
let report_short b r =
  match r with
  | Err e -> bprintf b "  error: %s\n" e
  | Ok l ->
      List.iter (fun ((ob : obligation), v) -> bprintf b "  [%s] %s\n" (label ob.ob_label) (verdict_short v)) l;
      bprintf b "  => %s\n" (if all_proved l then "accepted" else "rejected")

let run b name p env e = bprintf b "  run %s: %s\n" name (answer (evalFuel fuel p env e))

let run_fuel b name k p env e =
  bprintf b "  run %s with fuel %d: %s\n" name k (answer (evalFuel (zi k) p env e))

let client_text b (cl : client) =
  (match cl.cl_env with
   | [] -> ()
   | g -> bprintf b "  free: %s\n" (String.concat ", " (List.map (fun (x, t) -> x ^ ":" ^ ty t) g)));
  (match cl.cl_pre with [] -> () | ps -> bprintf b "  assumed: %s\n" (String.concat ", " (List.map formula ps)));
  bprintf b "%s\n  required: %s\n" (expr 4 cl.cl_expr) (formula cl.cl_post)

let wp_text b p s (cl : client) =
  bprintf b "  wp:\n%s\n" (wpf 4 (wp RuleName p s client_scope cl.cl_env cl.cl_expr cl.cl_post));
  bprintf b "  flattened:\n";
  List.iter
    (fun ob -> bprintf b "    [%s] %s\n" (label ob.ob_label) (obligation ob))
    (flatten cl.cl_pre (wp RuleName p s client_scope cl.cl_env cl.cl_expr cl.cl_post))

let arr l = VArr (List.map zi l)

(* ---- 1. contracts of functions ---- *)

let demo1 b =
  header b "1. Contracts of functions: f 1 + 2";
  section b "the program";
  bprintf b "%s\n" (program bounded bounded_spec);
  section b "the body against the contract";
  report b (check_prog prove bounded bounded_spec);
  section b "the client";
  client_text b client_f1;
  wp_text b bounded bounded_spec client_f1;
  report b (check_client prove bounded bounded_spec client_f1);
  run b "client" bounded [] client_f1.cl_expr;
  section b "the body replaced by 3: the contract and the check of the client stay";
  bprintf b "%s\n" (program bounded3 bounded_spec);
  report b (check_prog prove bounded3 bounded_spec);
  report b (check_client prove bounded3 bounded_spec client_f1);
  run b "client" bounded3 [] client_f1.cl_expr;
  section b "f 2 violates the precondition";
  client_text b client_f2;
  report b (check_client prove bounded bounded_spec client_f2);
  section b "so does f 2 with its result unused";
  client_text b client_f2_dropped;
  report b (check_client prove bounded bounded_spec client_f2_dropped);
  run b "client (the body does not fail)" bounded [] client_f2_dropped.cl_expr

(* ---- 2. the name of the result ---- *)

let demo2 b =
  header b "2. inc 0 = 1 through the name of the result";
  section b "the program";
  bprintf b "%s\n" (program inc_prog inc_spec);
  report b (check_prog prove inc_prog inc_spec);
  section b "the client";
  client_text b client_inc0;
  section b "the main rule: Post_inc(0, r) after the call";
  report b (check_client_with prove RuleName inc_prog inc_spec client_inc0);
  section b "the root rule APPc: Pre_inc(r.x) ∧ Post_inc(r.x, r) for a fresh r.x";
  report b (check_client_with prove RuleRoot inc_prog inc_spec client_inc0);
  section b "two calls f 0: fresh names of results are not the function symbol δ";
  client_text b client_twice;
  report b (check_client prove bounded bounded_spec client_twice);
  run b "client" bounded [] client_twice.cl_expr

(* ---- 3. the traversal of an array ---- *)

let infer_report b (log, ans) =
  bprintf b "  weakening:\n";
  List.iter (fun e -> bprintf b "  %s\n" (wevent e)) log;
  match ans with
  | Inferred (s, sol, rep) ->
      bprintf b "  inferred: %s\n" (solution sol);
      bprintf b "  the contracts after substitution:\n%s\n"
        (String.concat "\n"
           (List.map (fun fd -> "    " ^ fd.fd_name ^ " : " ^ contract_sig fd (contract_of s fd)) sum_prog));
      bprintf b "  rechecked by the first algorithm: %d obligations, %s\n" (List.length rep)
        (if all_proved rep then "all proved" else "NOT all proved")
  | IRefuted (ob, m) ->
      bprintf b "  refused at [%s]\n    %s\n    counter-model: %s\n" (label ob.ob_label) (obligation ob) (cmodel m)
  | IUndecided (ob, why) -> bprintf b "  undecided at [%s]\n    %s\n    %s\n" (label ob.ob_label) (obligation ob) why
  | IFailed why -> bprintf b "  failed: %s\n" why

let sum_runs b p =
  List.iter
    (fun l -> run b ("sum " ^ value (arr l)) p [ ("a", arr l) ] sum_def.fd_body)
    [ []; [ 1; 2; 3 ]; [ 5; -7; 11; 13 ] ]

let demo3 b =
  header b "3. The traversal of an array";
  section b "the program with the invariant given: 0 ≤ i ∧ i ≤ n";
  bprintf b "%s\n" (program sum_prog sum_spec);
  report b (check_prog prove sum_prog sum_spec);
  section b "the invariant as an unknown κ(i, n)";
  bprintf b "  Q = {%s}\n" (qualifiers Liquid.quals);
  infer_report b (infer prove sum_prog (sum_tspec quals) []);
  sum_runs b sum_prog;
  section b "termination of go: the measure n − i, a check of its own";
  report b (check_measures prove sum_prog sum_spec sum_measures);
  bprintf b "  the fuel of sum: 4·len a + 4 (sum_fuel, Examples/Sum.v)\n";
  List.iter (fun k -> run_fuel b "sum [1; 2; 3]" k sum_prog [ ("a", arr [ 1; 2; 3 ]) ] sum_def.fd_body) [ 15; 16 ];
  section b "the invariant 0 ≤ i alone: the reads are safe, the measure is not non-negative";
  report_short b (check_prog prove sum_prog sum_spec_lower);
  report b (check_measures prove sum_prog sum_spec_lower sum_measures);
  section b "the error of bounds: i ≤ n instead of i < n";
  infer_report b (infer prove sum_prog_le (sum_tspec quals) []);
  sum_runs b sum_prog_le;
  section b "an abstraction too coarse: Q without 0 ≤ i";
  bprintf b "  Q = {%s}\n" (qualifiers quals_no_lower);
  infer_report b (infer prove sum_prog (sum_tspec quals_no_lower) []);
  bprintf b "  the same program as in the first outcome:\n";
  sum_runs b sum_prog

(* ---- 4. divergence ---- *)

let demo4 b =
  header b "4. loop with the refinement false";
  section b "the program";
  bprintf b "%s\n" (program loop_prog loop_spec);
  report b (check_prog prove loop_prog loop_spec);
  section b "the client";
  client_text b client_loop;
  report b (check_client prove loop_prog loop_spec client_loop);
  List.iter (fun k -> run_fuel b "client on []" k loop_prog [ ("a", arr []) ] client_loop.cl_expr) [ 10; 100; 1000 ];
  section b "no measure: the call repeats the argument, μ < μ (loop_no_measure, Examples/Loop.v)";
  report b (check_measures prove loop_prog loop_spec loop_measures)

let all () =
  let b = Buffer.create 65536 in
  List.iter (fun d -> d b) [ demo1; demo2; demo3; demo4 ];
  Buffer.contents b
