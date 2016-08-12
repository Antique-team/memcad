(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_utils.ml
 **       utilities for numerical domain
 ** Xavier Rival, 2011/07/03 *)
open Data_structures
open Lib
open Nd_sig
(* External: Apron components *)
open Apron

(** Imrpovements for later:
 ** - is it possible to generate the widening steps once for all,
 **   for all variables
 ** - packing in the numeric domain **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "nd_uts__" and level = Log_level.DEBUG end)


(** Debugging *)
let debug_loc = false


(** Managing Apron variables *)
let make_var (n: int): Var.t =
  Var.of_string (Printf.sprintf "|%d|" n)


(** Atom printers *)
(* Nodes. *)
let node_2str (i: int): string = Printf.sprintf "N|%d|" i
let nodej_2str (i: int): string =
  Log.fatal_exn "nodej_2str"
(* Variables *)
let var_2int (v: Var.t): int =
  let str = Var.to_string v in
  let n = String.length str in
  if n <= 2 then Log.fatal_exn "inadequate variable name: %s" str;
  try int_of_string (String.sub str 1 (n-2))
  with _ -> Log.fatal_exn "non parseable variable name: %s" str
let var_2str (v: Var.t): string = node_2str (var_2int v)
let var_2str_namer (sn: sv_namer) (v: Var.t): string =
  let i = var_2int v in
  try IntMap.find i sn with Not_found -> node_2str i

(* Turning interval into string *)
let interv_2str (i: interval): string =
  let inf =
    match i.intv_inf with
    | None -> "]-oo"
    | Some a -> Printf.sprintf "[%d" a in
  let sup =
    match i.intv_sup with
    | None -> "+oo["
    | Some a -> Printf.sprintf "%d]" a in
  Printf.sprintf "%s,%s" inf sup


(** Apron interface helpers *)
(* Turning Apron level 0 structures into strings *)
let coeff_2str (c: Coeff.t): string =
  match c with
  | Coeff.Scalar scal -> Scalar.to_string scal
  | Coeff.Interval _ -> Log.fatal_exn "pp_coeff-interval"
let unop_2str (u: Texpr0.unop): string =
  match u with
  | Texpr0.Neg ->  "-"
  | Texpr0.Cast -> "cast"
  | Texpr0.Sqrt -> "sqrt"
let binop_2str (b: Texpr0.binop): string =
  match b with
  | Texpr0.Add -> "+"
  | Texpr0.Sub -> "-"
  | Texpr0.Mul -> "*"
  | Texpr0.Div -> "/"
  | Texpr0.Mod -> "%"
  | Texpr0.Pow -> "^"
let cons_op_2str (typ: Lincons0.typ): string =
  match typ with
  | Lincons1.EQ    -> "="
  | Lincons1.DISEQ -> "!="
  | Lincons1.SUP   -> ">"
  | Lincons1.SUPEQ -> ">="
  | Lincons1.EQMOD s -> Printf.sprintf "==(%s)" (Scalar.to_string s)
let cons_trailer_2str (typ: Lincons0.typ): string =
  match typ with
  | Lincons1.EQ    -> " = 0"
  | Lincons1.DISEQ -> " != 0"
  | Lincons1.SUP   -> " > 0"
  | Lincons1.SUPEQ -> " >= 0"
  | Lincons1.EQMOD s -> Printf.sprintf " == 0 (%s)" (Scalar.to_string s)
(* Turning Apron level 1 structures into strings *)
let texpr1_2str (sn: sv_namer) (te: Texpr1.t): string =
  let rec aux_expr (e: Texpr1.expr): string =
    match e with
    | Texpr1.Cst c -> coeff_2str c
    | Texpr1.Var v -> var_2str_namer sn v
    | Texpr1.Unop (u, te0, _, _) ->
        Printf.sprintf "%s (%s)" (unop_2str u) (aux_expr te0)
    | Texpr1.Binop (b, te0, te1, _, _) ->
        Printf.sprintf "(%s) %s (%s)"
          (aux_expr te0) (binop_2str b) (aux_expr te1) in
  aux_expr (Texpr1.to_expr te)
(* Debug pp for environments *)
let environment_2str (sn: sv_namer) (env: Environment.t): string =
  let ai, af = Environment.vars env in
  assert (Array.length af = 0);
  let isbeg = ref true in
  let s =
    Array.fold_left
      (fun (acc: string) (v: Var.t) ->
        let sep =
          if !isbeg then
            begin
              isbeg := false;
              ""
            end
          else "; " in
        Printf.sprintf "%s%s%s" acc sep (var_2str_namer sn v)
      ) "" ai in
  Printf.sprintf "[|%s|]" s


(* Extraction of integer variables *)
let get_ivars (env: Environment.t): Var.t array =
  let ivars, fvars = Environment.vars env in
  if Array.length fvars > 0 then Log.fatal_exn "unimp: floating-point vars";
  ivars

(* Turns a set of constraints into a string *)
let linconsarray_2stri (sn: sv_namer) (ind: string) (a: Lincons1.earray)
    : string =
  (* Extraction of the integer variables *)
  let env = a.Lincons1.array_env in
  let ivars = get_ivars env in
  (* pretty-printing of a constraint *)
  let f_lincons (cons: Lincons1.t): string =
    if Lincons1.is_unsat cons then Printf.sprintf "%sUNSAT\n" ind
    else
      (* print non zero coefficients *)
      let mt = ref false in
      let str0 =
        Array.fold_left
          (fun str v ->
            let c =
              try Lincons1.get_coeff cons v
              with exn ->
                Log.warn "get_coeff, var %s, exn %s"
                  (var_2str_namer sn v) (Printexc.to_string exn);
                Coeff.s_of_int 0 in
            if not (Coeff.is_zero c) then
              begin
                let var = var_2str_namer sn v in
                let str_ext = Printf.sprintf "%s . %s" (coeff_2str c) var in
                if !mt then
                  Printf.sprintf "%s + %s" str str_ext
                else
                  begin
                    mt := true;
                    str_ext
                  end
              end
            else str
          ) "" ivars in
      (* print the constant *)
      let str1 =
        let d0 = coeff_2str (Lincons1.get_cst cons) in
        if !mt then Printf.sprintf "%s + %s" str0 d0
        else d0 in
      (* print the relation *)
      Printf.sprintf "%s%s %s\n" ind str1
        (cons_trailer_2str (Lincons1.get_typ cons)) in
  (* Array of cons1 *)
  let ac1 =
    Array.mapi
      (fun i _ -> Lincons1.array_get a i)
      a.Lincons1.lincons0_array in
  Array.fold_left
    (fun (acc: string) cons ->
      Printf.sprintf "%s%s" acc (f_lincons cons)
    ) "" ac1

(** Numeric domain expressions *)
(* Conversion into strings and pretty-printing *)
let rec n_expr_2str: n_expr -> string = function
  | Ne_rand -> "rand"
  | Ne_csti i -> Printf.sprintf "%d" i
  | Ne_cstc c -> Printf.sprintf "%c" c
  | Ne_var iv -> Printf.sprintf "|%d|" iv
  | Ne_bin (b, e0, e1) ->
      Printf.sprintf "(%s) %s (%s)" (n_expr_2str e0) (binop_2str b)
        (n_expr_2str e1)
let n_cons_2str: n_cons -> string = function
  | Nc_rand -> "rand"
  | Nc_bool b ->
      Printf.sprintf "%b" b
  | Nc_cons (c, e0, e1) ->
      Printf.sprintf "%s %s %s" (n_expr_2str e0) (cons_op_2str c)
        (n_expr_2str e1)

(* Translation into Apron expressions, with environment *)
let rec translate_n_expr (env: Environment.t): n_expr -> Texpr1.t = function
  | Ne_rand -> Log.fatal_exn "translate_n_expr: rand"
  | Ne_csti i -> Texpr1.cst env (Coeff.s_of_int i)
  | Ne_cstc c -> Texpr1.cst env (Coeff.s_of_int (Char.code c))
  | Ne_var iv -> Texpr1.var env (make_var iv)
  | Ne_bin (b, e0, e1) ->
      Texpr1.binop b (translate_n_expr env e0)
        (translate_n_expr env e1) Texpr1.Int Texpr1.Near
let translate_n_cons (env: Environment.t): n_cons -> Tcons1.t = function
  | Nc_rand -> Log.fatal_exn "translate_n_cons: rand"
  | Nc_bool b ->
      if b then (* tautology constraint 0 = 0 *)
        let ex = translate_n_expr env (Ne_csti 0) in
        Tcons1.make ex Tcons1.EQ
      else (* anti-tautology constraint 1 = 0 *)
        let ex = translate_n_expr env (Ne_csti 1) in
        Tcons1.make ex Tcons1.EQ
  | Nc_cons (c, e0, e1) ->
      (*   e0 (c) e1    is translated into    e0 - e1 (c) 0   *)
      let ex = translate_n_expr env (Ne_bin (Texpr1.Sub, e0, e1)) in
      Tcons1.make ex c

(* Map translations *)
let rec n_expr_map (f: int -> int) (e: n_expr) =
  match e with
  | Ne_rand | Ne_cstc _ | Ne_csti _ -> e
  | Ne_var iv -> Ne_var (f iv)
  | Ne_bin (b, e0, e1) -> Ne_bin (b, n_expr_map f e0, n_expr_map f e1)
let n_cons_map (f: int -> int) (c: n_cons) =
  match c with
  | Nc_rand | Nc_bool _ -> c
  | Nc_cons (b, e0, e1) -> Nc_cons (b, n_expr_map f e0, n_expr_map f e1)

(* Substitutions *)
let rec n_expr_subst (f: int -> n_expr) (e: n_expr): n_expr =
  match e with
  | Ne_rand | Ne_cstc _ | Ne_csti _ -> e
  | Ne_var i -> f i
  | Ne_bin (b, e0, e1) -> Ne_bin (b, n_expr_subst f e0, n_expr_subst f e1)
let n_cons_subst (f: int -> n_expr): n_cons -> n_cons = function
  | (Nc_rand | Nc_bool _) as e -> e
  | Nc_cons (b, e0, e1) -> Nc_cons (b, n_expr_subst f e0, n_expr_subst f e1)

(* Iterators (for searching variables or verifying variables properties) *)
let rec n_expr_fold (f: int -> 'a -> 'a): n_expr -> 'a -> 'a =
  let rec aux (e: n_expr) (acc: 'a): 'a =
    match e with
    | Ne_rand | Ne_cstc _ | Ne_csti _ -> acc
    | Ne_var iv -> f iv acc
    | Ne_bin (_, e0, e1) -> aux e1 (aux e0 acc) in
  aux
let n_cons_fold (f: int -> 'a -> 'a) (c: n_cons) (acc: 'a): 'a =
  match c with
  | Nc_rand -> acc
  | Nc_bool _ -> acc
  | Nc_cons (b, e0, e1) -> n_expr_fold f e1 (n_expr_fold f e0 acc)

(* Check absence of Ne_rand *)
let rec n_expr_no_rand (e: n_expr): bool =
  match e with
  | Ne_rand -> false
  | Ne_cstc _ | Ne_csti _ | Ne_var _ -> true
  | Ne_bin (_, e0, e1) -> n_expr_no_rand e0 && n_expr_no_rand e1

(* Negation of an n_cons *)
let neg_n_cons: n_cons -> n_cons = function
  | Nc_rand -> Nc_rand
  | Nc_bool b -> Nc_bool (not b)
  | Nc_cons (Tcons1.EQ, e0, e1) -> Nc_cons (Tcons1.DISEQ, e0, e1)
  | Nc_cons (Tcons1.DISEQ, e0, e1) -> Nc_cons (Tcons1.EQ, e0, e1)
  | _ -> Log.fatal_exn "neg_n_cons"

(* Simplification of constraints, and pairs of expressions bound by an equality
 * or disequality constraint *)
let rec n_expr_simplify ((e0, e1): n_expr * n_expr): n_expr * n_expr =
  match e0, e1 with
  | Ne_bin (Texpr1.Mul, Ne_csti i0, ee0), Ne_bin (Texpr1.Mul, Ne_csti i1, ee1)
  | Ne_bin (Texpr1.Add, Ne_var i0, ee0), Ne_bin (Texpr1.Add, Ne_var i1, ee1) ->
      if i0 = i1 then n_expr_simplify (ee0, ee1)
      else e0, e1
  | _ -> e0, e1
let n_cons_simplify (c: n_cons): n_cons =
  match c with
  | Nc_cons (Tcons1.DISEQ as op, e0, e1)
  | Nc_cons (Tcons1.EQ    as op, e0, e1) ->
      let ee0, ee1 = n_expr_simplify (e0, e1) in
      if ee0 == e0 && ee1 = e1 then c
      else Nc_cons (op, ee0, ee1)
  | _ -> c

(* Decomposition to turn into a pair (base, offset),
 * when known to be an address
 * (may return None, if no decompisition is found) *)
let n_expr_decomp_base_off (e: n_expr): (int * n_expr) option =
  match e with
  | Ne_bin (Texpr1.Add, Ne_var i0, e1) -> Some (i0, e1)
  | _ -> None

(** Widening utilities: make constraints for widening thresholds *)
let make_widening_thresholds (env: Environment.t): Lincons1.earray =
  let avi, avf = Environment.vars env in
  assert (Array.length avf = 0);
  let nvars = Array.length avi
  and nthr = IntSet.cardinal !Flags.widen_thresholds in
  let ncons = 2 * nvars * nthr in
  let ea = Lincons1.array_make env ncons in
  let ctr: int ref = ref 0 in
  let push_cstr (lc: Lincons1.t): unit =
    Lincons1.array_set ea !ctr lc ;
    incr ctr in
  Array.iter
    (fun (v: Var.t) ->
      IntSet.iter
        (fun thr ->
          (* we should add two constraints:
           *  - x + c >= 0, i.e., x <= c
           *    x + c >= 0, i.e., x >= -c *)
          (* positive constraint:  - x + c >= 0 *)
          let lep = Linexpr1.make env in
          Linexpr1.set_list lep
            [ Coeff.s_of_int (-1), v ] (Some (Coeff.s_of_int thr));
          let lcp = Lincons1.make lep Lincons1.SUPEQ in
          push_cstr lcp;
          (* negative constraint:    x + c >= 0 *)
          let len = Linexpr1.make env in
          Linexpr1.set_list len
            [ Coeff.s_of_int 1, v ] (Some (Coeff.s_of_int thr));
          let lcn = Lincons1.make len Lincons1.SUPEQ in
          push_cstr lcn;
        ) !Flags.widen_thresholds
    ) avi;
  if debug_loc then
    Log.info "Widening threshold:\n%s"
      (linconsarray_2stri IntMap.empty "  " ea);
  ea


(** Mapping functions *)

(* Empty mapping *)
let node_mapping_empty: 'a node_mapping =
  { nm_map    = IntMap.empty;
    nm_rem    = IntSet.empty;
    nm_suboff = (fun _ -> true) }

(* Addition of a new node *)
let add_to_mapping (i: int) (j: int) (m: 'a node_mapping): 'a node_mapping =
  let map =
    try
      let k, s = IntMap.find i m.nm_map in
      IntMap.add i (k, IntSet.add j s) m.nm_map ;
    with
    | Not_found -> IntMap.add i (j, IntSet.empty) m.nm_map in
  { m with
    nm_map = map ;
    nm_rem = IntSet.remove i m.nm_rem }

(* Pretty-printing *)
let node_mapping_2str (m: 'a node_mapping): string =
  let smap =
    IntMap.fold
      (fun i (j, s) acc ->
        let ts = IntSet.fold (Printf.sprintf "%d;%s") s "" in
        Printf.sprintf "        %d -> %d;%s\n%s" i j ts acc
      ) m.nm_map "" in
  let srem = intset_2str m.nm_rem in
  Printf.sprintf "   [[Mapping:\n%s     Removed: %s]]\n" smap srem


(** Decomposition *)

(* Splitting of an expression into a pair formed of a variable
 * and a linear combination of factors *)
exception No_decomp of string
let decomp_lin (e: n_expr): int * n_expr =
  let rec aux (e: n_expr): int option * n_expr option =
    match e with
    | Ne_csti _ -> None, Some e
    | Ne_var i -> Some i, None
    | Ne_bin (Texpr1.Add, e0, e1) ->
        let v0, ee0 = aux e0 and v1, ee1 = aux e1 in
        let v =
          match v0, v1 with
          | None, v | v, None -> v
          | _, _ -> raise (No_decomp "decomp_lin: too many vars") in
        let ee =
          match ee0, ee1 with
          | None, ee | ee, None -> ee
          | Some eee0, Some eee1 -> Some (Ne_bin (Texpr1.Add, eee0, eee1)) in
        v, ee
    | _ -> None, Some e in
  match aux e with
  | Some v, Some ee -> v, ee
  | Some v, None -> v, Ne_csti 0
  | _, _ -> raise (No_decomp "decomp_lin failed")
let decomp_lin_opt (e: n_expr): (int * n_expr) option =
  try Some (decomp_lin e)
  with No_decomp _ -> None
