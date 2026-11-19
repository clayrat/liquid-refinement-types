(* The native reference: the generator, the obligations of measure, the
   difference solver and weakening written by hand, with the exact
   integers of Zarith.  It is self-contained: its syntax, of formulas,
   obligations, programs and templates, is declared here, and nothing of
   the extract is used, neither a type nor a function; the build compiles
   it where the extract is not visible.  diff.ml translates the examples
   of the extract into this syntax and compares the results.  The solver
   is independent of the one in Rocq: Floyd–Warshall for the longest
   paths instead of Bellman–Ford, linear forms as maps; an edge
   [a + w ≤ b] is entailed iff the graph is inconsistent or the longest
   path from [a] to [b] weighs at least [w]. *)

(* ---- syntax ---- *)

type term = TVar of string | TConst of Z.t | TAdd of term * term | TSub of term * term | TMul of Z.t * term | TLen of string
type batom = BVar of string | BConst of bool
type arg = UInt of term | UBool of batom

type formula =
  | FLe of term * term
  | FLt of term * term
  | FEq of term * term
  | FAtom of batom
  | FKappa of string * arg list
  | FAnd of formula * formula
  | FOr of formula * formula
  | FNot of formula

type sort = SInt | SBool

(* The origin of an obligation: the result of a scope, the precondition
   of a callee at the binding [x] in a scope, the measure of a function
   non-negative, or decreasing at the call bound to [x]. *)
type label =
  | LResult of string
  | LPre of string * string * string
  | LMeasureNonneg of string
  | LMeasureDecr of string * string

type obligation = { ob_label : label; ob_hyps : formula list; ob_goal : formula }

(* A counter-model: the integer variables, the booleans, the lengths. *)
type cmodel = { cm_int : (string * Z.t) list; cm_bool : (string * bool) list; cm_len : (string * Z.t) list }

type ty = TyInt | TyBool | TyUnit | TyArr
type atom = AVar of string | ANum of Z.t | ABool of bool | AUnit
type cmp = CLt | CLe | CEq
type cond = CAtom of atom | CCmp of cmp * atom * atom
type prim = PAdd | PSub | PLength | PGet

type expr =
  | ERet of atom
  | EPrim of string * prim * atom list * expr
  | ECall of string * string * atom list * expr
  | EIf of cond * expr * expr

type fundef = { fd_name : string; fd_params : (string * ty) list; fd_ret : ty; fd_body : expr }
type prog = fundef list
type contract = { c_pre : formula list; c_post : formula }
type spec = (string * contract) list
type client = { cl_env : (string * ty) list; cl_pre : formula list; cl_expr : expr; cl_post : formula }

type hole = { hl_name : string; hl_quals : formula list }
type rtemplate = { rt_fixed : formula; rt_hole : hole option }
type ctemplate = { ct_pre : rtemplate list; ct_post : rtemplate }
type tspec = (string * ctemplate) list
type kdecl = { kd_name : string; kd_formals : (string * sort) list; kd_quals : formula list }

(* ---- formulas ---- *)

let is_true = function FAtom (BConst true) -> true | _ -> false
let ftrue = FAtom (BConst true)
let ffalse = FAtom (BConst false)
let fand p q = if is_true p then q else if is_true q then p else FAnd (p, q)
let fconj ps = List.fold_right fand ps ftrue

let rec conjuncts = function
  | FAnd (p, q) -> conjuncts p @ conjuncts q
  | p -> if is_true p then [] else [ p ]

let rec kfree = function
  | FKappa _ -> false
  | FAnd (p, q) | FOr (p, q) -> kfree p && kfree q
  | FNot p -> kfree p
  | _ -> true

type sub = { ints : (string * term) list; bools : (string * batom) list; arrs : (string * string) list }

let empty = { ints = []; bools = []; arrs = [] }

let rec tsub s = function
  | TVar x -> (match List.assoc_opt x s.ints with Some t -> t | None -> TVar x)
  | TConst z -> TConst z
  | TAdd (a, b) -> TAdd (tsub s a, tsub s b)
  | TSub (a, b) -> TSub (tsub s a, tsub s b)
  | TMul (k, t) -> TMul (k, tsub s t)
  | TLen a -> TLen (match List.assoc_opt a s.arrs with Some b -> b | None -> a)

let bsub s = function BVar x -> (match List.assoc_opt x s.bools with Some b -> b | None -> BVar x) | b -> b
let asub s = function UInt t -> UInt (tsub s t) | UBool b -> UBool (bsub s b)

let rec fsub s = function
  | FLe (a, b) -> FLe (tsub s a, tsub s b)
  | FLt (a, b) -> FLt (tsub s a, tsub s b)
  | FEq (a, b) -> FEq (tsub s a, tsub s b)
  | FAtom b -> FAtom (bsub s b)
  | FKappa (k, us) -> FKappa (k, List.map (asub s) us)
  | FAnd (p, q) -> FAnd (fsub s p, fsub s q)
  | FOr (p, q) -> FOr (fsub s p, fsub s q)
  | FNot p -> FNot (fsub s p)

(* ---- semantics on a concrete valuation, κ read as false ---- *)

type valn = { vi : string -> Z.t; vb : string -> bool; vl : string -> Z.t }

let rec tev v = function
  | TVar x -> v.vi x
  | TConst z -> z
  | TAdd (a, b) -> Z.add (tev v a) (tev v b)
  | TSub (a, b) -> Z.sub (tev v a) (tev v b)
  | TMul (k, t) -> Z.mul k (tev v t)
  | TLen a -> v.vl a

let bev v = function BVar x -> v.vb x | BConst c -> c

let rec fev v = function
  | FLe (a, b) -> Z.leq (tev v a) (tev v b)
  | FLt (a, b) -> Z.lt (tev v a) (tev v b)
  | FEq (a, b) -> Z.equal (tev v a) (tev v b)
  | FAtom b -> bev v b
  | FKappa _ -> false
  | FAnd (p, q) -> fev v p && fev v q
  | FOr (p, q) -> fev v p || fev v q
  | FNot p -> not (fev v p)

let get l x d = match List.assoc_opt x l with Some z -> z | None -> d

let valn_of (m : cmodel) =
  { vi = (fun x -> get m.cm_int x Z.zero); vb = (fun b -> get m.cm_bool b false); vl = (fun a -> get m.cm_len a Z.zero) }

let falsifies (m : cmodel) (ob : obligation) =
  let v = valn_of m in
  List.for_all (fun (_, z) -> Z.leq Z.zero z) m.cm_len
  && List.for_all (fev v) ob.ob_hyps
  && not (fev v ob.ob_goal)

(* ---- the difference solver ---- *)

type nd = Zero | I of string | B of string | L of string

module NM = Map.Make (struct type t = nd let compare = compare end)

(* A linear form: coefficients and a constant. *)
type lf = Z.t NM.t * Z.t

let lconst c : lf = (NM.empty, c)
let lnode n : lf = (NM.singleton n Z.one, Z.zero)

let ladd ((m1, c1) : lf) ((m2, c2) : lf) : lf =
  (NM.union (fun _ a b -> let s = Z.add a b in if Z.equal s Z.zero then None else Some s) m1 m2, Z.add c1 c2)

let lscale k ((m, c) : lf) : lf = if Z.equal k Z.zero then lconst Z.zero else (NM.map (Z.mul k) m, Z.mul k c)

let rec lin = function
  | TVar x -> lnode (I x)
  | TConst z -> lconst z
  | TAdd (a, b) -> ladd (lin a) (lin b)
  | TSub (a, b) -> ladd (lin a) (lscale Z.minus_one (lin b))
  | TMul (k, t) -> lscale k (lin t)
  | TLen a -> lnode (L a)

(* An edge (a, w, b): a + w ≤ b. *)
type ed = nd * Z.t * nd

(* A constraint: an edge, true, false, or outside the fragment. *)
type con = Edge of ed | Yes | No | Out of formula

(* [0 ≤ l]. *)
let classify (l : lf) : con option =
  let m, c = l in
  match NM.bindings m with
  | [] -> Some (if Z.leq Z.zero c then Yes else No)
  | [ (x, k) ] when Z.equal k Z.one -> Some (Edge (Zero, Z.neg c, x))
  | [ (x, k) ] when Z.equal k Z.minus_one -> Some (Edge (x, Z.neg c, Zero))
  | [ (x, k); (y, k') ] when Z.equal k Z.one && Z.equal k' Z.minus_one -> Some (Edge (y, Z.neg c, x))
  | [ (y, k'); (x, k) ] when Z.equal k Z.one && Z.equal k' Z.minus_one -> Some (Edge (y, Z.neg c, x))
  | _ -> None

let le t1 t2 p = match classify (lin (TSub (t2, t1))) with Some c -> c | None -> Out p
let plus1 t = TAdd (t, TConst Z.one)

(* The constraints of [p] (pos) or of [¬p]. *)
let rec decomp pos p =
  match p, pos with
  | FLe (a, b), true -> [ le a b p ]
  | FLe (a, b), false -> [ le (plus1 b) a p ]
  | FLt (a, b), true -> [ le (plus1 a) b p ]
  | FLt (a, b), false -> [ le b a p ]
  | FEq (a, b), true -> [ le a b p; le b a p ]
  | FAtom (BConst c), _ -> if c = pos then [] else [ No ]
  | FAtom (BVar b), true -> [ Edge (Zero, Z.one, B b) ]
  | FAtom (BVar b), false -> [ Edge (B b, Z.zero, Zero) ]
  | FAnd (q, r), true | FOr (q, r), false -> decomp pos q @ decomp pos r
  | FNot q, _ -> decomp (not pos) q
  | _ -> [ Out p ]

(* Floyd–Warshall for the longest paths; [None] is minus infinity. *)
let longest nodes (es : ed list) =
  let n = Array.length nodes in
  let idx x = let rec go i = if nodes.(i) = x then i else go (i + 1) in go 0 in
  let d = Array.make_matrix n n None in
  for i = 0 to n - 1 do d.(i).(i) <- Some Z.zero done;
  List.iter
    (fun (a, w, b) ->
      let i = idx a and j = idx b in
      match d.(i).(j) with Some w' when Z.geq w' w -> () | _ -> d.(i).(j) <- Some w)
    es;
  for k = 0 to n - 1 do
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        match d.(i).(k), d.(k).(j) with
        | Some a, Some b -> (
            let s = Z.add a b in
            match d.(i).(j) with Some c when Z.geq c s -> () | _ -> d.(i).(j) <- Some s)
        | _ -> ()
      done
    done
  done;
  (d, idx)

let consistent nodes d = let ok = ref true in Array.iteri (fun i _ -> match d.(i).(i) with Some w when Z.gt w Z.zero -> ok := false | _ -> ()) nodes; !ok

let nodes_of (es : ed list) =
  let l = List.concat_map (fun (a, _, b) -> [ a; b ]) es in
  Array.of_list (List.sort_uniq compare (Zero :: l))

let side n = match n with B b -> [ (Zero, Z.zero, B b); (B b, Z.minus_one, Zero) ] | L a -> [ (Zero, Z.zero, L a) ] | _ -> []

(* A model of a consistent graph: the longest paths from a virtual
   source, relative to [0]. *)
let model_of (es : ed list) : cmodel =
  let nodes = nodes_of es in
  let d, idx = longest nodes es in
  let from x =
    Array.fold_left (fun acc y -> match d.(idx y).(idx x) with Some w when Z.gt w acc -> w | _ -> acc) Z.zero nodes
  in
  let z0 = from Zero in
  let vals = Array.to_list (Array.map (fun x -> (x, Z.sub (from x) z0)) nodes) in
  { cm_int = List.filter_map (function I x, z -> Some (x, z) | _ -> None) vals;
    cm_bool = List.filter_map (function B b, z -> Some (b, not (Z.equal z Z.zero)) | _ -> None) vals;
    cm_len = List.filter_map (function L a, z -> Some (a, z) | _ -> None) vals }

type nverdict = NProved | NRefuted of cmodel | NUnknown of string

let prove (ob : obligation) : nverdict =
  let hs = List.concat_map (decomp true) ob.ob_hyps in
  let hedges = List.concat_map (function Edge e -> [ e ] | No -> [ (Zero, Z.one, Zero) ] | _ -> []) hs in
  let gs = decomp true ob.ob_goal in
  if List.exists (function Out _ -> true | _ -> false) gs then NUnknown "the goal is outside the difference fragment"
  else
    let gedges = List.concat_map (function Edge e -> [ e ] | _ -> []) gs in
    let g = List.concat_map side (Array.to_list (nodes_of (hedges @ gedges))) @ hedges in
    let nodes = nodes_of (g @ gedges) in
    let d, idx = longest nodes g in
    let incons = not (consistent nodes d) in
    let counter es =
      let m = model_of es in
      if falsifies m ob then NRefuted m else NUnknown "the model of the fragment does not falsify the obligation"
    in
    let rec go = function
      | [] -> NProved
      | Yes :: rest -> go rest
      | No :: rest -> if incons then go rest else counter g
      | Edge (a, w, b) :: rest -> (
          if incons then go rest
          else
            match d.(idx a).(idx b) with
            | Some w' when Z.geq w' w -> go rest
            | _ -> counter ((b, Z.sub Z.one w, a) :: g))
      | Out _ :: _ -> NUnknown "the goal is outside the difference fragment"
    in
    go gs

(* ---- contracts and the generator ---- *)

let nu = "ν"

let contract_of (s : spec) (fd : fundef) =
  match List.assoc_opt fd.fd_name s with
  | Some c -> c
  | None -> { c_pre = List.map (fun _ -> ftrue) fd.fd_params; c_post = ftrue }

let prim_params = function
  | PAdd | PSub -> [ ("x", TyInt); ("y", TyInt) ]
  | PLength -> [ ("a", TyArr) ]
  | PGet -> [ ("a", TyArr); ("i", TyInt) ]

let prim_ret _ = TyInt

let prim_contract p =
  let v x = TVar x in
  match p with
  | PAdd -> { c_pre = [ ftrue; ftrue ]; c_post = FEq (v nu, TAdd (v "x", v "y")) }
  | PSub -> { c_pre = [ ftrue; ftrue ]; c_post = FEq (v nu, TSub (v "x", v "y")) }
  | PLength -> { c_pre = [ ftrue ]; c_post = FAnd (FEq (v nu, TLen "a"), FLe (TConst Z.zero, v nu)) }
  | PGet -> { c_pre = [ ftrue; FAnd (FLe (TConst Z.zero, v "i"), FLt (v "i", TLen "a")) ]; c_post = ftrue }

let prim_label = function PAdd -> "+" | PSub -> "-" | PLength -> "length" | PGet -> "get"

let aterm = function AVar x -> TVar x | ANum z -> TConst z | _ -> TConst Z.zero
let abatom = function AVar x -> BVar x | ABool b -> BConst b | _ -> BConst false

let bind x t a s =
  match t, a with
  | TyInt, _ -> { s with ints = (x, aterm a) :: s.ints }
  | TyBool, _ -> { s with bools = (x, abatom a) :: s.bools }
  | TyArr, AVar y -> { s with arrs = (x, y) :: s.arrs }
  | _ -> s

let rec inst ps args =
  match ps, args with (x, t) :: ps', a :: args' -> bind x t a (inst ps' args') | _ -> empty

let pre_inst c ps args = fconj (List.map (fsub (inst ps args)) c.c_pre)
let post_inst c ps ret args r = fsub (bind nu ret (AVar r) (inst ps args)) c.c_post

let atom_type g = function
  | AVar x -> (match List.assoc_opt x g with Some t -> t | None -> TyUnit)
  | ANum _ -> TyInt
  | ABool _ -> TyBool
  | AUnit -> TyUnit

let ret_inst t a psi = fsub (bind nu t a empty) psi

let cond_formula = function
  | CAtom a -> FAtom (abatom a)
  | CCmp (CLt, a, b) -> FLt (aterm a, aterm b)
  | CCmp (CLe, a, b) -> FLe (aterm a, aterm b)
  | CCmp (CEq, a, b) -> FEq (aterm a, aterm b)

let extend phi h = if is_true h then phi else phi @ [ h ]
let emit l h g = if is_true g then [] else [ { ob_label = l; ob_hyps = h; ob_goal = g } ]

let rec gen (p : prog) (s : spec) scope g phi e psi =
  match e with
  | ERet a -> emit (LResult scope) phi (ret_inst (atom_type g a) a psi)
  | EPrim (x, op, args, e') ->
      let c = prim_contract op and ps = prim_params op in
      emit (LPre (scope, prim_label op, x)) phi (pre_inst c ps args)
      @ gen p s scope ((x, prim_ret op) :: g) (extend phi (post_inst c ps (prim_ret op) args x)) e' psi
  | ECall (x, f, args, e') -> (
      match List.find_opt (fun fd -> fd.fd_name = f) p with
      | Some fd ->
          let c = contract_of s fd in
          emit (LPre (scope, f, x)) phi (pre_inst c fd.fd_params args)
          @ gen p s scope ((x, fd.fd_ret) :: g) (extend phi (post_inst c fd.fd_params fd.fd_ret args x)) e' psi
      | None -> emit (LPre (scope, f, x)) phi ffalse)
  | EIf (c, e1, e2) ->
      gen p s scope g (extend phi (cond_formula c)) e1 psi @ gen p s scope g (extend phi (FNot (cond_formula c))) e2 psi

let fun_obligations p s fd =
  let c = contract_of s fd in
  gen p s fd.fd_name fd.fd_params (List.fold_left extend [] c.c_pre) fd.fd_body c.c_post

let prog_obligations p s = List.concat_map (fun_obligations p s) p

let client_obligations p s (cl : client) =
  gen p s "client" cl.cl_env (List.fold_left extend [] cl.cl_pre) cl.cl_expr cl.cl_post

(* ---- measures ---- *)

(* The integer variables and the arrays under len of a term. *)
let rec tnames = function
  | TVar x -> ([ x ], [])
  | TConst _ -> ([], [])
  | TAdd (a, b) | TSub (a, b) ->
      let i1, a1 = tnames a and i2, a2 = tnames b in
      (i1 @ i2, a1 @ a2)
  | TMul (_, t) -> tnames t
  | TLen a -> ([], [ a ])

let rec decreases (p : prog) (s : spec) f ps mu phi e =
  match e with
  | ERet _ -> []
  | EPrim (x, op, args, e') ->
      let c = prim_contract op and pps = prim_params op in
      decreases p s f ps mu (extend phi (post_inst c pps (prim_ret op) args x)) e'
  | ECall (x, g, args, e') -> (
      match List.find_opt (fun fd -> fd.fd_name = g) p with
      | Some fd ->
          let c = contract_of s fd in
          let here = if g = f then emit (LMeasureDecr (f, x)) phi (FLt (tsub (inst ps args) mu, mu)) else [] in
          here @ decreases p s f ps mu (extend phi (post_inst c fd.fd_params fd.fd_ret args x)) e'
      | None -> [])
  | EIf (c, e1, e2) ->
      decreases p s f ps mu (extend phi (cond_formula c)) e1
      @ decreases p s f ps mu (extend phi (FNot (cond_formula c))) e2

(* The obligations of the measures, or the reason the measures are refused:
   a function the program does not define, two measures for one function,
   a name other than an integer parameter or an array parameter. *)
let measure_obligations (p : prog) (s : spec) (m : (string * term) list) =
  let names = List.map fst m in
  let find f = List.find_opt (fun fd -> fd.fd_name = f) p in
  let scoped (fd : fundef) mu =
    let ints, arrs = tnames mu in
    List.for_all (fun x -> List.mem (x, TyInt) fd.fd_params) ints
    && List.for_all (fun a -> List.mem (a, TyArr) fd.fd_params) arrs
  in
  if List.length (List.sort_uniq compare names) <> List.length names then Error "two measures for one function"
  else
    match List.find_opt (fun (f, mu) -> match find f with Some fd -> not (scoped fd mu) | None -> true) m with
    | Some (f, _) -> Error ("an unknown function or a name out of scope in the measure of " ^ f)
    | None ->
        Ok
          (List.concat_map
             (fun (fd : fundef) ->
               match List.assoc_opt fd.fd_name m with
               | Some mu ->
                   let h = List.fold_left extend [] (contract_of s fd).c_pre in
                   emit (LMeasureNonneg fd.fd_name) h (FLe (TConst Z.zero, mu))
                   @ decreases p s fd.fd_name fd.fd_params mu h fd.fd_body
               | None -> [])
             p)

(* ---- Liquid inference ---- *)

let sorted g =
  List.filter_map (fun (x, t) -> match t with TyInt -> Some (x, SInt) | TyBool -> Some (x, SBool) | _ -> None) g

let formal_arg (x, s) = match s with SInt -> UInt (TVar x) | SBool -> UBool (BVar x)

let inst_rt vis (rt : rtemplate) =
  match rt.rt_hole with
  | None -> (rt.rt_fixed, [])
  | Some h ->
      let fs = sorted vis in
      (fand rt.rt_fixed (FKappa (h.hl_name, List.map formal_arg fs)), [ { kd_name = h.hl_name; kd_formals = fs; kd_quals = h.hl_quals } ])

(* [Error] for a template of an unknown function, a second template of
   the same function, or a number of refinements other than the arity:
   nothing is dropped. *)
exception Bad_template of string

let instantiate (p : prog) (t : tspec) =
  let names = List.map fst t in
  if List.length (List.sort_uniq compare names) <> List.length names then Error "two templates for one function"
  else
    try
      Ok
        (List.fold_right
           (fun (f, ct) (s, ds) ->
             match List.find_opt (fun fd -> fd.fd_name = f) p with
             | None -> raise (Bad_template ("a template for an unknown function: " ^ f))
             | Some fd ->
                 let rec pres seen ps rts =
                   match ps, rts with
                   | [], [] -> ([], [])
                   | q :: ps', rt :: rts' ->
                       let r, d = inst_rt (q :: seen) rt in
                       let rs, ds' = pres (seen @ [ q ]) ps' rts' in
                       (r :: rs, d @ ds')
                   | _ -> raise (Bad_template ("the number of refinements in the template of " ^ f))
                 in
                 let pre, d1 = pres [] fd.fd_params ct.ct_pre in
                 let post, d2 = inst_rt ((nu, fd.fd_ret) :: fd.fd_params) ct.ct_post in
                 ((f, { c_pre = pre; c_post = post }) :: s, d1 @ d2 @ ds))
           t ([], []))
    with Bad_template why -> Error why

let kinst d us q =
  let rec bindk fs us s =
    match fs, us with
    | (x, _) :: fs', UInt t :: us' -> let s = bindk fs' us' s in { s with ints = (x, t) :: s.ints }
    | (x, _) :: fs', UBool b :: us' -> let s = bindk fs' us' s in { s with bools = (x, b) :: s.bools }
    | _ -> s
  in
  fsub (bindk d.kd_formals us empty) q

let rec apply_sol ds sol p =
  match p with
  | FKappa (k, us) -> (
      match List.find_opt (fun d -> d.kd_name = k) ds, List.assoc_opt k sol with
      | Some d, Some qs -> fconj (List.map (kinst d us) qs)
      | _ -> p)
  | FAnd (a, b) -> fand (apply_sol ds sol a) (apply_sol ds sol b)
  | FOr (a, b) -> FOr (apply_sol ds sol a, apply_sol ds sol b)
  | FNot a -> FNot (apply_sol ds sol a)
  | _ -> p

type nhorn = { label : label; hyps : formula list; goal : [ `K of string * arg list | `F of formula ] }

let normalize (ob : obligation) =
  let hs = List.concat_map conjuncts ob.ob_hyps in
  List.map (fun g -> { label = ob.ob_label; hyps = hs; goal = (match g with FKappa (k, us) -> `K (k, us) | g -> `F g) })
    (conjuncts ob.ob_goal)

type nanswer =
  | NInferred of (string * formula list) list
  | NRefusedAt of obligation * cmodel
  | NUndecided of obligation
  | NFailed of string

(* The removed qualifiers in order, and the answer. *)
let infer (p : prog) (t : tspec) (cls : client list) =
  match instantiate p t with
  | Error why -> ([], NFailed why)
  | Ok (s, ds) ->
  let obs = List.concat_map (client_obligations p s) cls @ prog_obligations p s in
  let hs = List.concat_map normalize obs in
  if List.exists (fun h -> not (List.for_all (function FKappa _ -> true | f -> kfree f) h.hyps)
                           || (match h.goal with `F g -> not (kfree g) | _ -> false)) hs
  then ([], NFailed "shape")
  else
    let removed = ref [] in
    let sol = ref (List.map (fun d -> (d.kd_name, d.kd_quals)) ds) in
    let exception Stop of nanswer in
    try
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter
          (fun h ->
            match h.goal with
            | `F _ -> ()
            | `K (k, us) ->
                let d = List.find (fun d -> d.kd_name = k) ds in
                let a = List.map (apply_sol ds !sol) h.hyps in
                let qs = List.assoc k !sol in
                let kept =
                  List.filter
                    (fun q ->
                      let ob = { ob_label = h.label; ob_hyps = a; ob_goal = kinst d us q } in
                      match prove ob with
                      | NProved -> true
                      | NRefuted _ -> removed := (k, q) :: !removed; false
                      | NUnknown _ -> raise (Stop (NUndecided ob)))
                    qs
                in
                if List.length kept < List.length qs then changed := true;
                sol := List.map (fun (k', qs') -> if k' = k then (k', kept) else (k', qs')) !sol)
          hs
      done;
      List.iter
        (fun h ->
          match h.goal with
          | `K _ -> ()
          | `F g -> (
              let ob = { ob_label = h.label; ob_hyps = List.map (apply_sol ds !sol) h.hyps; ob_goal = g } in
              match prove ob with
              | NProved -> ()
              | NRefuted m -> raise (Stop (NRefusedAt (ob, m)))
              | NUnknown _ -> raise (Stop (NUndecided ob))))
        hs;
      (List.rev !removed, NInferred !sol)
    with Stop a -> (List.rev !removed, a)
