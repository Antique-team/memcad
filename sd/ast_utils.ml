(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ast_utils.ml
 **       utilities on abstract syntax trees
 ** Xavier Rival, 2011/05/27 *)
open Data_structures
open Flags
open Lib
open Apron
open Ast_sig
open Nd_sig

(** Error report *)
module Log =
  Logger.Make(struct let section = "ast_uts_" and level = Log_level.DEBUG end)

(** Some basic iterators on expressions, lvalues and set properties *)
let rec map_expr (f: 'a -> 'b) (e: 'a expr): 'b expr =
  match e with
  | Erand -> Erand
  | Ecst c -> Ecst c
  | Euni (o, e0) -> Euni (o, map_texpr f e0)
  | Ebin (o, e0, e1) -> Ebin (o, map_texpr f e0, map_texpr f e1)
  | Elval lv -> Elval (map_tlval f lv)
  | EAddrOf lv -> EAddrOf (map_tlval f lv)
and map_texpr (f: 'a -> 'b) (e, t) = map_expr f e, t
and map_lval (f: 'a -> 'b) (l: 'a lval): 'b lval =
  match l with
  | Lvar v -> Lvar (f v)
  | Lderef e -> Lderef (map_texpr f e)
  | Lfield (l, off) -> Lfield (map_tlval f l, off)
  | Lindex (l, e) -> Lindex (map_tlval f l, map_texpr f e)
and map_tlval (f: 'a -> 'b) (l, t) = map_lval f l, t
let map_setprop (f: 'a -> 'b) (g: setvar -> int)  (s: 'a tlval setprop)
    : 'b tlval setprop =
  match s with
  | Sp_sub (l, r) -> Sp_sub ( { l with s_uid = g l }, { r with s_uid = g r } )
  | Sp_mem (l, r) -> Sp_mem (map_tlval f l, { r with s_uid = g r } )
  | Sp_emp l -> Sp_emp { l with s_uid = g l }
  | Sp_euplus (l, i, r) ->
      Sp_euplus ({ l with s_uid = g l }, map_tlval f i, { r with s_uid = g r })

(** Named types *)
let tnamed_types: typ StringMap.t ref = ref StringMap.empty
let tnamed_find (n: string): typ =
  StringMap.find n !tnamed_types
let tnamed_add (n: string) (t: typ): unit =
  tnamed_types := StringMap.add n t !tnamed_types

(** Utilities on types *)
let rec alignof_typ (t: typ): int =
  match t with
  | Tunk -> Log.fatal_exn "align of [unknown-type]"
  | Tint (sz,_) -> sz
  | Tfloat _ -> Flags.abi_ptr_size
  | Tptr _ -> Flags.abi_ptr_size
  | Tbool -> Flags.abi_bool_size
  | Tchar -> Flags.abi_char_size
  | Tstring _ -> Flags.abi_char_size
  | Tstruct s -> s.ts_align
  | Tunion tu -> tu.tu_align
  | Tarray (tu, _) -> alignof_typ tu
  | Tnamed n -> alignof_typ (tnamed_find n)
  | Tvoid -> 1
let rec sizeof_typ (t: typ): int =
  match t with
  | Tunk -> Log.fatal_exn "size of [unknown-type]"
  | Tint (sz,_) -> sz
  | Tfloat sz -> sz
  | Tptr _ -> Flags.abi_ptr_size
  | Tbool -> Flags.abi_bool_size
  | Tchar -> Flags.abi_char_size
  | Tstring n -> Flags.abi_char_size * n
  | Tstruct s -> s.ts_size
  | Tunion tu -> tu.tu_size
  | Tarray (t0,nb) -> nb * sizeof_typ t0
  | Tnamed n -> sizeof_typ (tnamed_find n)
  | Tvoid -> 1
let find_field (s: typ_struct) (fld: string): typ_sfield =
  let l =
    List.filter (fun f -> String.compare f.tsf_name fld = 0) s.ts_fields in
  match l with
  | [ ]   -> Log.fatal_exn "find_field_offset: none found"
  | [ f ] -> f
  | _     -> Log.fatal_exn "find_field_offset: too many found"
let field_2off (f: field): Offs.t =
  match f.f_off with
  | None   -> Offs.of_string f.f_name
  | Some i -> Offs.of_field (f.f_name, i)
let typ_is_ptr: typ -> bool = function
  | Tptr _ -> true
  | _ -> false


(** Pretty-printing of expressions, and lvalues *)
let tsign_2str: tsign -> string = function
  | Tsigned   -> "signed"
  | Tunsigned -> "unsigned"
let tisize_2str: tisize -> string = function
  | 1 -> "char"
  | 2 -> "short"
  | 4 -> "int"
  | _ -> Log.fatal_exn "unbound size of int type"
let field_names_of_struct s =
  List.map (fun f -> f.tsf_name) s.ts_fields
let field_names_of_union u =
  List.map (fun f -> f.tuf_name) u.tu_fields
let struct_2str s =
  gen_list_2str "" (fun x -> x) "; " (field_names_of_struct s)
let union_2str u =
  gen_list_2str "" (fun x -> x) "; " (field_names_of_union u)
let rec typ_2str: typ -> string = function
  | Tunk -> "[unknown-type]"
  | Tint (i, s) -> Printf.sprintf "%s %s" (tsign_2str s) (tisize_2str i)
  | Tfloat 4 -> "float"
  | Tfloat 8 -> "double"
  | Tfloat _ -> Log.fatal_exn "unbound size of float type"
  | Tptr None -> "(?)*"
  | Tptr (Some t) -> Printf.sprintf "(%s)*" (typ_2str t)
  | Tbool -> "bool"
  | Tchar -> "char"
  | Tstring n -> Printf.sprintf "char[%d]" n
  | Tstruct s -> Printf.sprintf "struct: {%s}" (struct_2str s)
  | Tunion  u -> Printf.sprintf "union: {%s}"  (union_2str  u)
  | Tarray (t0,nb) -> Printf.sprintf "%s[%d]" (typ_2str t0) nb
  | Tnamed n -> Printf.sprintf "type[%s]" n
  | Tvoid -> "void"
let uni_op_2str: uni_op -> string = function
  | Uneg -> "-"
  | Unot -> "!"
  | Ubnot -> "~"
let bin_op_2str: bin_op -> string = function
  | Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "*"
  | Bdiv -> "/"
  | Bmod -> "%"
  | Beq  -> "=="
  | Bgt  -> ">"
  | Bge  -> ">="
  | Bne  -> "!="
  | Band -> "&&"
  | Bor  -> "||"
let const_2str: const -> string = function
  | Cint i -> string_of_int i
  | Cint64 ii -> Int64.to_string ii
  | Cchar c -> Printf.sprintf "\'%c\'" c
  | Cstring s -> Printf.sprintf "\"%s\"" s
let field_2str (off: field): string = off.f_name
let arith_2str (a2s: 'a -> string) =
  let rec aux_expr0: 'a expr -> string = function
    | Ebin ((Band | Bor) as o, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_texpr1 e0) (bin_op_2str o) (aux_texpr1 e1)
    | e -> aux_expr1 e
  and aux_expr1: 'a expr -> string = function
    | Ebin ((Beq | Bgt | Bge | Bne) as o, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_texpr1 e0) (bin_op_2str o) (aux_texpr2 e1)
    | e -> aux_expr2 e
  and aux_expr2: 'a expr -> string = function
    | Ebin ((Badd | Bsub) as o, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_texpr2 e0) (bin_op_2str o) (aux_texpr3 e1)
    | e -> aux_expr3 e
  and aux_expr3: 'a expr -> string = function
    | Ebin ((Bmul | Bdiv | Bmod) as o, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_texpr3 e0) (bin_op_2str o) (aux_texpr4 e1)
    | e -> aux_expr4 e
  and aux_expr4: 'a expr -> string = function
    | Euni (o, e0) ->
        Printf.sprintf "%s %s" (uni_op_2str o) (aux_texpr5 e0)
    | e -> aux_expr5 e
  and aux_expr5: 'a expr -> string = function
    | Erand -> "rand"
    | Ecst c -> const_2str c
    | Elval lv -> aux_tlval lv
    | EAddrOf lv -> Printf.sprintf "& %s" (aux_tlval lv)
    | e -> Printf.sprintf "(%s)" (aux_expr0 e)
  and aux_texpr0 (e, t) = aux_expr0 e
  and aux_texpr1 (e, t) = aux_expr1 e
  and aux_texpr2 (e, t) = aux_expr2 e
  and aux_texpr3 (e, t) = aux_expr3 e
  and aux_texpr4 (e, t) = aux_expr4 e
  and aux_texpr5 (e, t) = aux_expr5 e
  and aux_lval: 'a lval -> string = function
    | Lvar x -> a2s x
    | Lderef e -> Printf.sprintf "(* %s)" (aux_texpr3 e)
    | Lfield (l, f) -> Printf.sprintf "%s.%s" (aux_tlval l) (field_2str f)
    | Lindex (l, e) -> Printf.sprintf "%s[%s]" (aux_tlval l) (aux_texpr0 e)
  and aux_tlval (l, t) = aux_lval l in
  aux_expr0, aux_texpr0, aux_lval, aux_tlval
let expr_2str  a2s = let f, _, _, _ = arith_2str a2s in f
let texpr_2str a2s = let _, f, _, _ = arith_2str a2s in f
let lval_2str  a2s = let _, _, f, _ = arith_2str a2s in f
let tlval_2str a2s = let _, _, _, f = arith_2str a2s in f
let condtree_2str a2s =
  let rec aux = function
    | Ctrand -> "rand"
    | Ctleaf ex -> texpr_2str a2s ex
    | Ctland (c0, c1) -> Printf.sprintf "(%s) /\\ (%s)" (aux c0) (aux c1)
    | Ctlor (c0, c1) -> Printf.sprintf "(%s) \\/ (%s)" (aux c0) (aux c1) in
  aux

(** Printers for c-vars based expressions *)
let var_2str (v: var): string =
  if Flags.flag_debug_uids then Printf.sprintf "%s<%d>" v.v_name v.v_id
  else v.v_name
let vexpr_2str:  var  expr -> string =  expr_2str var_2str
let vtexpr_2str: var texpr -> string = texpr_2str var_2str
let vlval_2str:  var  lval -> string =  lval_2str var_2str
let vtlval_2str: var tlval -> string = tlval_2str var_2str
let vcondtree_2str: var condtree -> string = condtree_2str var_2str

(** Printers for int *)
let nid_2str: int -> string = Printf.sprintf "N|%d|"
let iexpr_2str:  int  expr -> string =  expr_2str nid_2str
let itexpr_2str: int texpr -> string = texpr_2str nid_2str
let ilval_2str:  int  lval -> string =  lval_2str nid_2str
let itlval_2str: int tlval -> string = tlval_2str nid_2str
let icondtree_2str: int condtree -> string = condtree_2str nid_2str

(** Typing *)
(* Basic functions to check correctness of types, combine them, etc *)
let is_typ_int: typ -> bool = function
  | Tint (_, _) -> true
  | _ -> false
let cst_typ: const -> typ = function
  | Cint _ -> Tint (4, Tsigned)
  | Cint64 _ -> Tint (8, Tsigned)
  | Cchar _ -> Tchar
  | Cstring s -> Tstring (String.length s)
let int_promotion (sz0, sg0) (sz1, sg1) =
  if sz0 = sz1 && sg0 = sg1 then (sz0, sg1)
  else Log.todo_exn "non trivial integer promotion"
let bin_typ (b: bin_op) (t0: typ) (t1: typ) =
  match b, t0, t1 with
  | Bgt, Tint _, Tint _
  | Bge, Tint _, Tint _
  | Beq, Tint _, Tint _ -> Tbool
  | Badd, Tint (sz0, sg0), Tint (sz1, sg1) ->
      let sz, sg = int_promotion (sz0, sg0) (sz1, sg1) in
      Tint (sz, sg)
  | _, _, _ ->
      Log.fatal_exn "bin_typ: %s, %s, %s"
        (bin_op_2str b) (typ_2str t0) (typ_2str t1)
(* Computing well typed expressions and conditions *)
let rec type_texpr (m: var -> typ) (e: var texpr): var texpr =
  type_expr m (fst e)
and type_expr (m: var -> typ) (e: var expr): var texpr =
  match e with
  | Erand -> Log.todo_exn "typ rand"
  | Ecst c -> e, cst_typ c
  | Euni _ -> Log.todo_exn "typ uni"
  | Ebin (b, te0, te1) ->
      let ne0 = type_texpr m te0 and ne1 = type_texpr m te1 in
      let nt = bin_typ b (snd ne0) (snd ne1) in
      Ebin (b, ne0, ne1), nt
  | Elval lv -> let nlv = type_tlval m lv in Elval nlv, snd nlv
  | EAddrOf lv ->
      let nlv = type_tlval m lv in
      EAddrOf nlv, Tptr (Some (snd nlv))
and type_tlval (m: var -> typ) (l: var tlval): var tlval =
  type_lval m (fst l)
and type_lval (m: var -> typ) (l: var lval): var tlval =
  match l with
  | Lvar x ->
      let t =
        try m x
        with Not_found ->
          Log.warn "type not found for var %s\n" (var_2str x);
          Tunk in
      l, t
  | Lderef e ->
      let ne = type_texpr m e in
      begin
        match snd ne with
        | Tptr (Some t) -> Lderef ne, t
        | _ -> Log.fatal_exn "not a valid pointer type"
      end
  | Lfield (lv, f) ->
      let nlv = type_tlval m lv in
      let tfield =
        let tstruct =
          match snd nlv with
          | Tstruct p -> p
          | _ -> Log.fatal_exn "not a valid struct type" in
        find_field tstruct f.f_name in
      Lfield (nlv, f), tfield.tsf_typ
  | Lindex (lv, e) ->
      let nlv = type_tlval m lv and ne = type_texpr m e in
      begin
        match snd nlv, snd ne with
        | Tptr (Some t), Tint _ -> Lindex (nlv, ne), t
        | _, _ ->  Log.fatal_exn "type Log.fatal_exn on array dereference"
      end


(** Binding *)
let bind_var (f: string -> int) (v: var): var =
  try { v with v_id = f v.v_name }
  with Not_found -> Log.fatal_exn "variable %s does not exist" (var_2str v)
let bind_texpr (f: string -> int) = map_texpr (bind_var f)
let bind_tlval (f: string -> int) = map_tlval (bind_var f)


(** Extraction of condition trees *)
(* Simply pulls condition operators at the top into another ast.
 * This will make treatment of the guard operator easier *)
let rec extract_tree (e: 'a texpr): 'a condtree =
  match fst e with
  | Ebin ((Beq | Bne), (Erand, _), _) | Ebin ((Beq | Bne), _, (Erand, _))
  | Erand -> Ctrand
  | Ebin (Band, e0, e1) -> Ctland (extract_tree e0, extract_tree e1)
  | Ebin (Bor, e0, e1)  -> Ctlor  (extract_tree e0, extract_tree e1)
  | _ -> Ctleaf e


(** Translation of operators *)
let tr_bin_op: bin_op -> Texpr1.binop = function
  | Badd -> Texpr1.Add
  | Bsub -> Texpr1.Sub
  | Bmul -> Texpr1.Mul
  | Bdiv -> Texpr1.Div
  | Bmod -> Texpr1.Mod
  | b -> Log.fatal_exn "not arithmetic binop: %s" (bin_op_2str b)


(** Translation of conditions *)
(* Utilities *)
let texpr_is_rand_cell: 'a texpr -> bool = function
  | Erand, _ -> true
  | _ -> false
let texpr_is_const: 'a texpr -> bool = function
  | Ecst _, _ -> true
  | _ -> false
let make_apron_op: bin_op -> Lincons0.typ = function
  | Bgt -> Tcons1.SUP   (* e0 - e1 > 0 *)
  | Bge -> Tcons1.SUPEQ (* e0 - e1 >= 0 *)
  | Beq -> Tcons1.EQ    (* e0 - e1 = 0 *)
  | Bne -> Tcons1.DISEQ (* e0 - e1 != 0 *)
  | _   -> Log.fatal_exn "impossible branch"
(* Generic function
 * (actually, cannot be used as is in dom_shape_flat *)
let gen_tr_tcond
    (f: 'a -> int texpr -> 'a * n_expr)
    (t: 'a) (c: int texpr): 'a * n_cons =
  match fst c with
  | Ecst (Cint i) -> (* 0: false, otherwise: true *)
      t, Nc_bool (i != 0)
  | Ebin ((Bgt | Bge | Beq | Bne) as op, e0, e1) ->
      if (texpr_is_rand_cell e0 && texpr_is_const e1
        || texpr_is_const e0 && texpr_is_rand_cell e1) then
        t, Nc_rand
      else
        let aop = make_apron_op op in
        let t, te0 = f t e0 in
        let t, te1 = f t e1 in
        t, Nc_cons (aop, te0, te1)
  | Elval _ -> (* amounts to e != 0 *)
      let r, te = f t c in
      let te_zero = Ne_csti 0 in
      t, Nc_cons (Tcons1.DISEQ, te, te_zero)
  | Ebin (Band, e0, e1) ->
      Log.todo_exn "tr_cond &&"
  | _ ->
      Log.todo_exn "tr_tcond: %s" (itexpr_2str c)
