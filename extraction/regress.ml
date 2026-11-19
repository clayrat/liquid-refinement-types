(* Regression tests of the extract: the output of the demonstrations
   against lecture9.expected, the answers the lecture relies on, and the
   exact integers of Zarith beyond the machine int — in the arithmetic of
   the evaluator and in the sums of weights when cycles are checked. *)
open Liquid
open Pretty

let failures = ref 0
let checks = ref 0

let expect name actual expected =
  incr checks;
  if actual <> expected then begin
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  actual:   %s\n" name expected actual
  end

let expect_true name b = expect name (string_of_bool b) "true"

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let fuel = zi 1000
let big e = Big_int_Z.power_int_positive_int 2 e
let accepted_r r = accepted r

(* The demonstrations, verbatim. *)
let () =
  let actual = Demos.all () in
  let expected = read_file "lecture9.expected" in
  incr checks;
  if actual <> expected then begin
    incr failures;
    let a = String.split_on_char '\n' actual and e = String.split_on_char '\n' expected in
    let rec first i a e =
      match a, e with
      | x :: a', y :: e' -> if x = y then first (i + 1) a' e' else Printf.printf "FAIL demos: line %d\n  expected: %s\n  actual:   %s\n" i y x
      | x :: _, [] -> Printf.printf "FAIL demos: line %d\n  expected: <end>\n  actual:   %s\n" i x
      | [], y :: _ -> Printf.printf "FAIL demos: line %d\n  expected: %s\n  actual:   <end>\n" i y
      | [], [] -> ()
    in
    first 1 a e
  end

(* The answers of the lecture. *)
let () =
  expect_true "f: body accepted" (accepted_r (check_prog prove bounded bounded_spec));
  expect_true "f 1 + 2 accepted" (accepted_r (check_client prove bounded bounded_spec client_f1));
  expect_true "f = 3: body accepted" (accepted_r (check_prog prove bounded3 bounded_spec));
  expect_true "f 2 rejected" (not (accepted_r (check_client prove bounded bounded_spec client_f2)));
  expect_true "f 2 unused rejected" (not (accepted_r (check_client prove bounded bounded_spec client_f2_dropped)));
  expect "f 1 + 2 runs" (answer (evalFuel fuel bounded [] client_f1.cl_expr)) "Value 4";
  expect "f = 3: f 1 + 2 runs" (answer (evalFuel fuel bounded3 [] client_f1.cl_expr)) "Value 5";
  expect_true "inc 0 = 1 accepted" (accepted_r (check_client_with prove RuleName inc_prog inc_spec client_inc0));
  expect_true "inc 0 = 1 refuted by APPc"
    (match check_client_with prove RuleRoot inc_prog inc_spec client_inc0 with
     | Ok [ (_, Refuted _) ] -> true
     | _ -> false);
  expect_true "go/sum accepted" (accepted_r (check_prog prove sum_prog sum_spec));
  expect_true "go/sum with ≤ rejected" (not (accepted_r (check_prog prove sum_prog_le sum_spec)));
  expect_true "loop accepted" (accepted_r (check_prog prove loop_prog loop_spec));
  expect_true "loop client accepted" (accepted_r (check_client prove loop_prog loop_spec client_loop));
  expect_true "inference: success"
    (match snd (infer prove sum_prog (sum_tspec quals) []) with Inferred _ -> true | _ -> false);
  expect_true "inference: error of bounds"
    (match snd (infer prove sum_prog_le (sum_tspec quals) []) with IRefuted _ -> true | _ -> false);
  expect_true "inference: Q too coarse"
    (match snd (infer prove sum_prog (sum_tspec quals_no_lower) []) with IRefuted _ -> true | _ -> false);
  (* gen is the unfolding of wp, on every function of the examples. *)
  List.iter
    (fun (p, s) ->
      List.iter
        (fun fd ->
          let c = contract_of s fd in
          let pre = List.filter (fun h -> not (is_ftrue h)) c.c_pre in
          expect_true ("gen = flatten wp: " ^ fd.fd_name)
            (gen RuleName p s fd.fd_name fd.fd_params pre fd.fd_body c.c_post
             = flatten pre (wp RuleName p s fd.fd_name fd.fd_params fd.fd_body c.c_post)))
        p)
    [ (bounded, bounded_spec); (inc_prog, inc_spec); (sum_prog, sum_spec); (loop_prog, loop_spec) ]

(* Malformed input is refused, not trimmed: a template of an unknown
   function, two refinements for one parameter, two templates or two
   contracts for one function. *)
let () =
  let failed r = match snd r with IFailed _ -> true | _ -> false in
  let inc_two_pres =
    { ct_pre = [ { rt_fixed = ftrue; rt_hole = None }; { rt_fixed = ffalse; rt_hole = None } ];
      ct_post = (of_contract inc_contract).ct_post } in
  expect_true "a template of an unknown function is refused"
    (failed (infer prove sum_prog (sum_tspec quals @ [ ("typo", of_contract inc_contract) ]) []));
  expect_true "two refinements for one parameter are refused" (failed (infer prove inc_prog [ ("inc", inc_two_pres) ] []));
  expect_true "two templates for one function are refused"
    (failed (infer prove sum_prog (sum_tspec quals @ [ ("go", go_template quals_no_lower) ]) []));
  expect_true "two contracts for one function are refused"
    (not (accepted_r (check_prog prove bounded (bounded_spec @ [ ("f", { c_pre = [ ffalse ]; c_post = ftrue }) ]))))

(* Termination: the measures of the lecture, and the fuel of sum
   (sum_fuel in Examples/Sum.v) exact: 4·len a + 3 times out, 4·len a + 4
   returns the sum. *)
let () =
  let is_err = function Err _ -> true | Ok _ -> false in
  expect_true "measure n − i of go accepted" (accepted_r (check_measures prove sum_prog sum_spec sum_measures));
  expect_true "measure n − i under 0 ≤ i alone rejected"
    (accepted_r (check_prog prove sum_prog sum_spec_lower)
     && not (accepted_r (check_measures prove sum_prog sum_spec_lower sum_measures)));
  expect_true "measure n of go rejected" (not (accepted_r (check_measures prove sum_prog sum_spec [ ("go", TVar "n") ])));
  expect_true "loop has no measure" (not (accepted_r (check_measures prove loop_prog loop_spec loop_measures)));
  expect_true "a measure of an unknown function is refused"
    (is_err (check_measures prove sum_prog sum_spec (sum_measures @ [ ("typo", TVar "x") ])));
  expect_true "two measures for one function are refused"
    (is_err (check_measures prove sum_prog sum_spec (sum_measures @ [ ("go", TVar "n") ])));
  expect_true "a measure over a local is refused"
    (is_err (check_measures prove sum_prog sum_spec [ ("go", TSub (TVar "n", TVar "j")) ]));
  List.iter
    (fun l ->
      let l = List.map zi l @ [ big 70 ] in
      let n = List.length l in
      let total = List.fold_left Big_int_Z.add_big_int (zi 0) l in
      let name = Printf.sprintf "sum of length %d" n in
      expect (name ^ " with fuel 4n + 3") (answer (run_fun (zi (4 * n + 3)) sum_prog "sum" [ VArr l ])) "Timeout";
      expect (name ^ " with fuel 4n + 4") (answer (run_fun (zi (4 * n + 4)) sum_prog "sum" [ VArr l ]))
        ("Value " ^ zs total);
      expect_true (name ^ ": zsum") (zsum l = total))
    [ []; [ 1 ]; [ 1; 2 ]; [ -3; 5; 8 ]; [ 0; 0; 0; 0 ]; [ 7; -7; 7; -7; 7 ] ]

(* Exact integers beyond the machine int. *)
let () =
  (* the evaluator *)
  expect "inc 2^100" (answer (run_fun fuel inc_prog "inc" [ VInt (big 100) ]))
    ("Value " ^ zs (Big_int_Z.succ_big_int (big 100)));
  expect "sum [2^80; 2^80; -1]"
    (answer (evalFuel fuel sum_prog [ ("a", VArr [ big 80; big 80; zi (-1) ]) ] sum_def.fd_body))
    ("Value " ^ zs (Big_int_Z.pred_big_int (big 81)));
  (* the solver: the weights of the cycle sum beyond 2^62 *)
  let x = TVar "x" and y = TVar "y" in
  let ob g = { ob_label = LResult "big"; ob_hyps = [ FEq (x, TConst (big 70)); FEq (y, TAdd (x, TConst (big 70))) ]; ob_goal = g } in
  let proved = ob (FEq (y, TConst (big 71))) in
  expect_true "2^70 + 2^70 = 2^71 proved"
    (match prove proved with Proved c -> check_cert proved c | _ -> false);
  let refuted = ob (FLt (y, TConst (big 71))) in
  expect_true "2^70 + 2^70 < 2^71 refuted"
    (match prove refuted with
     | Refuted m -> check_counter m refuted && List.assoc "y" m.cm_int = big 71
     | _ -> false);
  (* a certificate is checked, not trusted: a forged cycle is rejected *)
  let forged = [ CertCycle (Some ((NInt "y", zi 0), NZero), [ ((NZero, big 63), NZero) ]) ] in
  expect_true "a forged certificate is rejected" (not (check_cert proved forged))

let () =
  Printf.printf "%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
