(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_utils.ml
 **       utilities for the "small-C" frontend
 ** Xavier Rival, 2011/07/15 *)
open C_sig
open Flags
open Data_structures
open Lib
open Ast_sig


(** Error handling *)
module Log =
  Logger.Make(struct let section = "c_uts___" and level = Log_level.DEBUG end)

(** Helpers for the parsing *)
(* Creation of variables *)
let make_c_var (s: string) (typ: c_type): c_var =
  { cv_name     = s;
    cv_uid      = -1;
    cv_type     = typ;
    cv_volatile = false }
(* Creation of type-less typed expressions and l-values *)
let mkve (e: c_exprk): c_expr =
  { cek = e ;
    cet = Ctvoid (* at reation time, in parsers *) }
let mkvl (l: c_lvalk): c_lval =
  { clk = l ;
    clt = Ctvoid (* at reation time, in parsers *) }
(* Transformation of one type into another *)
let unbox_clval_in_cexpr (e: c_expr): c_lval =
  match e.cek with
  | Celval l -> l
  | _ -> Log.fatal_exn "unbox_clval_in_cexpr"
let unbox_cstat_block (s: c_stat): c_block =
  match s.csk with
  | Csblock b -> b
  | _ -> [ s ]
let unbox_cstat_in_declaration: parsed_declaration -> c_stat = function
  | Pcd_var (v, l) -> { csk = Csdecl v ; csl = l }
  | Pcd_type _ -> Log.fatal_exn "unbox_cstat_in_declaration"
let unbox_c_var_in_declaration: parsed_declaration -> c_var = function
  | Pcd_var (v, _) -> v
  | Pcd_type _ -> Log.fatal_exn "unbox_c_var_in_declaration"
(* managing environments *)
let empty_unit: c_prog =
  { cp_vars  = StringMap.empty ;
    cp_funs  = StringMap.empty ;
    cp_types = StringMap.empty ;
    cp_aggs  = StringMap.empty }
let add_fundef (typ, name, params, body) (u: c_prog): c_prog =
  assert (not (StringMap.mem name u.cp_vars)) ;
  let cf = { cf_type = typ ;
             cf_uid  = -1 ;
             cf_name = name ;
             cf_args = params ;
             cf_body = body } in
  { u with cp_funs = StringMap.add name cf u.cp_funs }
let add_typedef (pcd: parsed_declaration) (u: c_prog): c_prog =
  match pcd with
  | Pcd_type (s, t) -> { u with cp_types = StringMap.add s t u.cp_types }
  | Pcd_var (v, i) ->
      assert (not (StringMap.mem v.cv_name u.cp_vars));
      { u with cp_vars = StringMap.add v.cv_name v u.cp_vars }

(** Pretty-printing of C abstract syntax trees *)
let rec c_type_2stri ?(decl: bool = false) (ind: string) (t: c_type): string =
  let f_agg_field_list (f: c_agg_field list): string =
    let nind = "  "^ind in
    let l =
      List.map
        (fun fld ->
          Printf.sprintf "%s%s %s;\n"
            nind (c_type_2stri ~decl:decl nind fld.caf_typ) fld.caf_name
        ) f in
    String.concat "" l in
  match t with
  | Ctchar -> "char"
  | Ctint -> "int"
  | Ctvoid -> "void"
  | Ctnamed n -> n.cnt_name
  | Ctstruct (Cad_named n) -> Printf.sprintf "struct %s" n
  | Ctunion  (Cad_named n) -> Printf.sprintf "union %s" n
  | Ctstruct (Cad_def s) ->
      let s0 =
        match s.cag_name with
        | None -> "struct"
        | Some n -> Printf.sprintf "struct %s" n in
      if decl then s0
      else Printf.sprintf "%s {\n%s%s}" s0 (f_agg_field_list s.cag_fields) ind
  | Ctunion (Cad_def u) ->
      if decl then "union { ... }"
      else Printf.sprintf "union {\n%s%s}" (f_agg_field_list u.cag_fields) ind
  | Ctptr None -> "(?) *"
  | Ctptr (Some t) -> Printf.sprintf "%s *" (c_type_2stri ~decl:decl ind t)
  | Ctarray (t, Some n) ->
      Printf.sprintf "%s[%d]" (c_type_2stri ~decl:decl ind t) n
  | Ctarray (t, None)   ->
      Printf.sprintf "%s[]"   (c_type_2stri ~decl:decl ind t)
  | Ctstring n -> Printf.sprintf "char[%d]" n
let c_type_2str ?(decl: bool = false): c_type -> string =
  c_type_2stri ~decl:decl ""
let c_typedef_2stri (ind: string) ((s, td): string * c_type): string =
  Printf.sprintf "%stypedef %s %s;\n" ind (c_type_2stri ind td) s
let c_const_2str (c: c_const): string =
  match c with
  | Ccint i -> Printf.sprintf "%d" i
  | Ccchar c -> Printf.sprintf "\'%c\'" c
  | Ccstring s -> Printf.sprintf "\"%s\"" s
  | Ccnull -> "null"
let c_uniop_2str: c_uniop -> string = function
  | Cuneg -> "-"
  | Culnot -> "!"
  | Cubnot -> "~"
let c_binop_2str: c_binop -> string = function
  | Cbeq -> "=="
  | Cbne -> "!="
  | Cbge -> ">="
  | Cble -> "<="
  | Cblt -> "<"
  | Cbgt -> ">"
  | Cbadd -> "+"
  | Cbmul -> "*"
  | Cbsub -> "-"
  | Cbmod -> "%"
  | Cbdiv -> "/"
  | Cbland -> "&&"
  | Cblor  -> "||"
  | Cbband -> "&"
  | Cbbor  -> "|"
  | Cbbslft -> "<<"
  | Cbbsrgh -> ">>"
let c_var_2str (v: c_var): string =
  Printf.sprintf "%s<%d,%s,%s>"
    v.cv_name v.cv_uid (c_type_2str ~decl:true v.cv_type)
    (string_of_bool v.cv_volatile)
let rec c_exprk_2str (e: c_exprk): string =
  let rec aux_basic e =
    match e with
    | Ceconst c -> c_const_2str c
    | Celval l -> c_lval_2str l
    | Ceaddrof l0 ->
        Printf.sprintf "&( %s )" (c_lval_2str l0)
    | Ceuni (u, e0) ->
        Printf.sprintf "%s (%s)" (c_uniop_2str u) (c_expr_2str e0)
    | _ -> Printf.sprintf "(%s)" (aux_log_or e)
  and aux_cast e = aux_basic e
  and aux_mult = function
    | Cebin (Cbmul, e0, e1) ->
        Printf.sprintf "%s * %s" (aux_mult e0.cek) (aux_cast e1.cek)
    | Cebin (Cbmod, e0, e1) ->
        Printf.sprintf "%s %% %s" (aux_mult e0.cek) (aux_cast e1.cek)
    | Cebin (Cbdiv, e0, e1) ->
        Printf.sprintf "%s / %s" (aux_mult e0.cek) (aux_cast e1.cek)
    | e -> aux_cast e
  and aux_add = function
    | Cebin (Cbadd | Cbsub as b, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_add e0.cek) (c_binop_2str b) (aux_mult e1.cek)
    | e -> aux_mult e
  and aux_shift = function
    | Cebin (((Cbbslft | Cbbsrgh) as b), e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_shift e0.cek) (c_binop_2str b) (aux_add e1.cek)
    | e -> aux_add e
  and aux_relational = function
    | Cebin (Cbge | Cbgt | Cble | Cblt as b, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_relational e0.cek) (c_binop_2str b) (aux_shift e1.cek)
    | e -> aux_shift e
  and aux_eq = function
    | Cebin (Cbeq | Cbne as b, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_eq e0.cek) (c_binop_2str b) (aux_relational e1.cek)
    | e -> aux_relational e
  and aux_and e = aux_eq e
  and aux_exc_or e = aux_and e
  and aux_inc_or e = aux_exc_or e
  and aux_log_and = function
    | Cebin (Cbland | Cbband as b, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_log_and e0.cek) (c_binop_2str b) (aux_inc_or e1.cek)
    | e -> aux_inc_or e
  and aux_log_or = function
    | Cebin (Cblor | Cbbor as b, e0, e1) ->
        Printf.sprintf "%s %s %s"
          (aux_log_or e0.cek) (c_binop_2str b) (aux_log_and e1.cek)
    | e -> aux_log_and e in
  aux_log_or e
and c_expr_2str (e: c_expr): string = c_exprk_2str e.cek
and c_lvalk_2str (l: c_lvalk): string =
  match l with
  | Clvar v -> c_var_2str v
  | Clfield (l, f) ->
      Printf.sprintf "%s.%s" (c_lval_2str l) f
  | Clderef e ->
      Printf.sprintf "*( %s )" (c_expr_2str e)
  | Clindex (l, e) ->
      Printf.sprintf "%s[%s]" (c_lval_2str l) (c_expr_2str e)
and c_lval_2str (l: c_lval): string = c_lvalk_2str l.clk
let c_decl_2stri (ind: string) (v: c_var): string =
  Printf.sprintf "%s%s %s" ind (c_type_2stri ~decl:true ind v.cv_type)
    (c_var_2str v)
let c_memcad_iparam_2str (ip: c_memcad_iparam): string =
  match ip with
  | Cmp_const i -> string_of_int i
  | Cmp_lval lv -> c_lval_2str lv
let c_memcad_setvar_2str (s: c_memcad_setvar): string =
  Printf.sprintf "%s<%d>" s.mc_setvar_name s.mc_setvar_uid
let c_memcad_setvars_2str (l: c_memcad_setvar list): string =
  gen_list_2str "" c_memcad_setvar_2str ", " l
let c_memcad_iparams_opt_2str (op: c_memcad_iparams option): string =
  match op with
  | None -> ""
  | Some p ->
      let f = gen_list_2str "" c_memcad_iparam_2str ", " in
      Printf.sprintf ", [%s | %s | %s]"
        (f p.mc_pptr) (f p.mc_pint) (c_memcad_setvars_2str p.mc_pset)
let rec c_memcad_setexprs_2str (ses: c_memcad_setexpr list): string =
  let c_memcad_setexpr_2str ( se: c_memcad_setexpr ): string =
    match se with
    | Cmp_subset (i, j) ->
        Printf.sprintf "%s $sub$ %s" (c_memcad_setvar_2str i)
          (c_memcad_setvar_2str j)
    | Cmp_mem (clv, j) ->
        Printf.sprintf "%s $in %s" (c_lval_2str clv) (c_memcad_setvar_2str j)
    | Cmp_empty i ->
        Printf.sprintf "%s = $empty" (c_memcad_setvar_2str i)
    | Cmp_euplus (i, clv, j) ->
        Printf.sprintf "%s = %s $uplus %s" (c_memcad_setvar_2str i)
          (c_lval_2str clv) (c_memcad_setvar_2str j)
  in gen_list_2str "" c_memcad_setexpr_2str ", " ses
let c_memcad_numexpr_2str
    (op: c_binop) (lv: c_lval) (i: c_memcad_iparam): string =
  Printf.sprintf "%s %s %s"
    (c_binop_2str op) (c_lval_2str lv) (c_memcad_iparam_2str i)
let c_memcad_numexprs_2str (exprs: c_num_expr list): string =
  gen_list_2str "" (fun (op, lv, i) -> c_memcad_numexpr_2str op lv i) ", " exprs
let c_memcad_2stri (mc: c_memcad_com): string =
  match mc with
  | Mc_add_inductive (lv, None, _) ->
      Printf.sprintf "add_inductive( %s )" (c_lval_2str lv)
  | Mc_add_inductive (lv, Some iname, op) ->
      Printf.sprintf "add_inductive( %s, %s%s )" (c_lval_2str lv) iname
        (c_memcad_iparams_opt_2str op)
  | Mc_add_segment (lv, iname, op, lve, inamee, ope) ->
      Printf.sprintf "add_segment( %s, %s%s *= %s, %s%s )"
        (c_lval_2str lv) iname
        (c_memcad_iparams_opt_2str op) (c_lval_2str lve) inamee
        (c_memcad_iparams_opt_2str ope)
  | Mc_assume num_exprs ->
      Printf.sprintf "assume( %s )" (c_memcad_numexprs_2str num_exprs)
  | Mc_check_segment (lv, iname, op, lve, inamee, ope) ->
      Printf.sprintf "check_segment( %s, %s%s *= %s, %s%s )"
        (c_lval_2str lv) iname
        (c_memcad_iparams_opt_2str op) (c_lval_2str lve) inamee
        (c_memcad_iparams_opt_2str ope)
  | Mc_add_setexprs ses ->
      Printf.sprintf
        "add_setexprs( %s )" (c_memcad_setexprs_2str ses)
  | Mc_decl_setvars ss ->
      Printf.sprintf "decl_setvars( %s )" (c_memcad_setvars_2str ss)
  | Mc_check_setexprs ses ->
      Printf.sprintf "check_setexprs( %s )" (c_memcad_setexprs_2str ses)
  | Mc_check_inductive (lv, None, _) ->
      Printf.sprintf "check_inductive( %s )" (c_lval_2str lv)
  | Mc_check_inductive (lv, Some iname, op) ->
      Printf.sprintf "check_inductive( %s, %s%s )" (c_lval_2str lv) iname
        (c_memcad_iparams_opt_2str op)
  | Mc_check_bottomness b ->
      Printf.sprintf "check_bottomness( %b )" b
  | Mc_unfold lv ->
      Printf.sprintf "unfold( %s )" (c_lval_2str lv)
  | Mc_unfold_bseg lv ->
      Printf.sprintf "unfold_bseg( %s )" (c_lval_2str lv)
  | Mc_unroll i ->
      Printf.sprintf "unroll( %d )" i
  | Mc_merge -> "merge"
  | Mc_sel_merge lv ->
      Printf.sprintf "sel_merge( %s )" (gen_list_2str "" c_var_2str ", " lv)
  | Mc_output_ext (Out_dot (vars, opts)) ->
      let str_list_to_string = gen_list_2str "" (fun x -> x) ", " in
      Printf.sprintf "output_dot( [ %s ], [ %s ] )"
        (str_list_to_string vars) (str_list_to_string opts)
  | Mc_output_stdout -> "output_stdout( )"
  | Mc_force_live lv ->
      Printf.sprintf "force_live( %s )" (gen_list_2str "" c_var_2str ", " lv)
  | Mc_kill_flow -> "kill_flow"
  | Mc_array_check -> "array_check"
  | Mc_array_assume -> "array_assume"
  | Mc_reduce_localize lv ->
      Printf.sprintf "reduce_localize( %s )" (c_lval_2str lv)
  | Mc_reduce_eager -> "reduce_eager"
  | Mc_comstring s -> s
let c_call_2str (c: c_call): string =
  Printf.sprintf "%s( %s )" (c_expr_2str c.cc_fun)
    (gen_list_2str "" c_expr_2str ", " c.cc_args)
let rec c_stat_2stri (ind: string) (s: c_stat): string =
  match s.csk with
  | Csdecl d ->
      Printf.sprintf "%s%s;\n" ind (c_decl_2stri "" d)
  | Csassign (lv, ex) ->
      Printf.sprintf "%s%s = %s;\n" ind (c_lval_2str lv) (c_expr_2str ex)
  | Cspcall c ->
      Printf.sprintf "%s%s;\n" ind (c_call_2str c)
  | Csfcall (lv, c) ->
      Printf.sprintf "%s%s = %s;\n" ind (c_lval_2str lv) (c_call_2str c)
  | Csif (c, b0, b1) ->
      let nind = Printf.sprintf "  %s" ind in
      if b1 = [] then
        Printf.sprintf "%sif( %s ){\n%s%s}\n"
          ind (c_expr_2str c) (c_block_2stri nind b0) ind
      else
        Printf.sprintf "%sif( %s ){\n%s%s} else {\n%s%s}\n"
          ind (c_expr_2str c) (c_block_2stri nind b0)
          ind (c_block_2stri nind b1) ind
  | Csblock b ->
      let nind = Printf.sprintf "  %s" ind in
      Printf.sprintf "%s{\n%s%s}\n" ind (c_block_2stri nind b) ind
  | Cswhile (e, b, None) ->
      let nind = Printf.sprintf "  %s" ind in
      Printf.sprintf "%swhile( %s ){\n%s%s}\n"
        ind (c_expr_2str e) (c_block_2stri nind b) ind
  | Cswhile (e, b, Some u) ->
      let nind = Printf.sprintf "  %s" ind in
      Printf.sprintf "%s_memcad( \"unroll( %d )\" );\n%swhile( %s ){\n%s%s}\n"
        ind u ind (c_expr_2str e) (c_block_2stri nind b) ind
  | Csreturn None ->
      Printf.sprintf "%sreturn;\n" ind
  | Csreturn (Some e) ->
      Printf.sprintf "%sreturn %s;\n" ind (c_expr_2str e)
  | Csbreak ->
      Printf.sprintf "%sbreak;\n" ind
  | Cscontinue ->
      Printf.sprintf "%scontinue;\n" ind
  | Csexit ->
      Printf.sprintf "exit(_);\n"
  | Cs_memcad c ->
      Printf.sprintf "%s_memcad( \"%s\" );\n" ind (c_memcad_2stri c)
  | Csassert e ->
      Printf.sprintf "%sassert( %s );\n" ind (c_expr_2str e)
  | Csalloc (l, e) ->
      Printf.sprintf "%s%s = malloc( %s );\n" ind
        (c_lval_2str l) (c_expr_2str e)
  | Csfree l ->
      Printf.sprintf "%sfree( %s );\n" ind (c_lval_2str l)
and c_block_2stri (ind: string) (l: c_block): string =
  match l with
  | [ ] -> ""
  | s0 :: l1 ->
      Printf.sprintf "%s%s" (c_stat_2stri ind s0) (c_block_2stri ind l1)
let funargs_2str (l: c_var list): string =
  gen_list_2str "" (c_decl_2stri "") ", " l
let c_fun_2stri (ind: string) (cf: c_fun): string =
  let nind = Printf.sprintf "  %s" ind in
  Printf.sprintf "%s%s %s( %s ){\n%s%s}\n"
    ind (c_type_2stri ind cf.cf_type) cf.cf_name (funargs_2str cf.cf_args)
    (c_block_2stri nind cf.cf_body) ind
let c_prog_2stri (ind: string) (cp: c_prog): string =
  let ltypes =
    StringMap.fold
      (fun s td (acc: string list) -> c_typedef_2stri ind (s, td) :: acc)
      cp.cp_types [ ] in
  let ldecls =
    StringMap.fold
      (fun _ v (acc: string list) -> c_decl_2stri ind v :: acc)
      cp.cp_vars [ ] in
  let lfuns =
    StringMap.fold
      (fun _ cf (acc: string list) -> c_fun_2stri ind cf :: acc)
      cp.cp_funs [ ] in
  String.concat "" (ltypes @ ldecls @ lfuns)

(** Other pp support stuffs *)
let c_stat_do_pp_status (s: c_stat): bool =
  match s.csk with
  | Csdecl _ -> !Flags.flag_status_decl
  | Csblock _ -> !Flags.flag_status_block
  | _ -> true

(** Extraction of program elements *)
let get_function (p: c_prog) (s: string): c_fun =
  try StringMap.find s p.cp_funs
  with Not_found -> Log.fatal_exn "function %s not found" s

(** Types and storage *)
(* Functions to elaborate representation of types, with size and align info *)
let rec c_type_elaborate (w: StringSet.t) (t: c_type): c_type =
  match t with
  | Ctvoid | Ctint | Ctchar | Ctstring _ -> t
  | Ctnamed cn ->
      if StringSet.mem cn.cnt_name w then t
      else
        let w = StringSet.add cn.cnt_name w in
        Ctnamed { cn with cnt_type = c_type_elaborate w cn.cnt_type }
  | Ctstruct (Cad_named _)
  | Ctunion  (Cad_named _) -> t
  | Ctstruct (Cad_def st) ->
      let l =
        List.map
          (fun fld -> { fld with
                        caf_typ = c_type_elaborate w fld.caf_typ }
          ) st.cag_fields in
      let s, a, l =
        List.fold_left
          (fun (s, a, l) fld ->
            let align = c_type_alignof fld.caf_typ
            and size  = c_type_sizeof fld.caf_typ in
            let pad =
              let delta = s mod align in
              if delta = 0 then 0
              else align - delta in
            let off = s + pad in
            off + size, max a align, { fld with
                                       caf_off  = off;
                                       caf_size = size; } :: l
          ) (0, -1, []) l in
      if s <= 0 || a <= 0 then
        Log.fatal_exn "c_type_elaborate: struct w/ s or a <= 0"
      else Ctstruct (Cad_def { cag_name   = st.cag_name;
                               cag_align  = a;
                               cag_size   = s;
                               cag_fields = List.rev l })
  | Ctunion (Cad_def u) ->
      let l =
        List.map
          (fun fld ->
            let utyp = c_type_elaborate w fld.caf_typ in
            let size = c_type_sizeof utyp in
            { fld with
              caf_off  = 0;
              caf_size = size;
              caf_typ  = utyp }
          ) u.cag_fields in
      let s, a =
        List.fold_left
          (fun (accs, acca) fld ->
            let align = c_type_alignof fld.caf_typ in
            max accs fld.caf_size, max acca align
          ) (-1, -1) l in
      if s <= 0 || a <= 0 then Log.fatal_exn "c_type_elaborate: union"
      else Ctunion (Cad_def { cag_name   = u.cag_name ;
                              cag_align  = a ;
                              cag_size   = s ;
                              cag_fields = l })
  | Ctptr tu -> Ctptr (Option.map (c_type_elaborate w) tu)
  | Ctarray (tu, n) -> Ctarray (c_type_elaborate w tu, n)
(* Functions to read the align and types *)
and c_type_alignof: c_type -> int = function
  | Ctvoid -> 1
  | Ctint -> 4
  | Ctchar -> 1
  | Ctstring _ -> 1
  | Ctnamed n -> c_type_alignof n.cnt_type
  | Ctstruct (Cad_named n)
  | Ctunion  (Cad_named n) ->
      Log.fatal_exn "align: aggregate %s w/o definition" n
  | Ctstruct (Cad_def cd)
  | Ctunion  (Cad_def cd)  -> let a = cd.cag_align in assert (a > 0); a
  | Ctptr _ -> Flags.abi_ptr_size
  | Ctarray (t, _) -> c_type_alignof t
and c_type_sizeof: c_type -> int = function
  | Ctvoid -> 1
  | Ctint -> 4
  | Ctchar -> 1
  | Ctstring n -> n * c_type_sizeof Ctchar
  | Ctnamed n -> c_type_sizeof n.cnt_type
  | Ctstruct (Cad_named n)
  | Ctunion  (Cad_named n) ->
      Log.fatal_exn "sizeof: aggregate %s w/o definition" n
  | Ctstruct (Cad_def cd)
  | Ctunion  (Cad_def cd) ->
      let a = cd.cag_size in assert (a > 0); a
  | Ctptr _ -> Flags.abi_ptr_size
  | Ctarray (t, Some n) -> n * (c_type_sizeof t)
  | Ctarray (t, None)   -> Log.fatal_exn "c_type_sizeof: incomplete array"
(* Elaboration function without extra argument *)
let c_type_elaborate (t: c_type): c_type = c_type_elaborate StringSet.empty t

(** Utility functions on expressions *)
(* Negation of conditions *)
let rec c_expr_neg (e: c_expr): c_expr =
  match e.cek with
  | Cebin (Cbge, e0, e1) -> { e with cek = Cebin (Cblt, e0, e1) }
  | Cebin (Cbgt, e0, e1) -> { e with cek = Cebin (Cble, e0, e1) }
  | Cebin (Cble, e0, e1) -> { e with cek = Cebin (Cbgt, e0, e1) }
  | Cebin (Cblt, e0, e1) -> { e with cek = Cebin (Cbge, e0, e1) }
  | Cebin (Cbeq, e0, e1) -> { e with cek = Cebin (Cbne, e0, e1) }
  | Cebin (Cbne, e0, e1) -> { e with cek = Cebin (Cbeq, e0, e1) }
  | Ceuni (Culnot, e0) -> { e with cek = e0.cek } (* double negation *)
  | Ceconst (Ccint i) ->
      if i = 0 then
        (* negation of false, we make this a one, represents true value *)
        { e with cek = Ceconst (Ccint 1) }
      else
        (* negation of true, zero represents false value *)
        { e with cek = Ceconst (Ccint 0) }
  | Cebin ((Cbband | Cbbor | Cblor) as op, e0, e1) ->
      let neg_op =
        match op with
        | Cbband -> Cbbor
        | Cbbor  -> Cbband
        | Cblor  -> Cbland
        | _ -> Log.fatal_exn "neg-op: %s" (c_binop_2str op) in
      let ne0 = c_expr_neg e0
      and ne1 = c_expr_neg e1 in
      { e with cek = Cebin (neg_op, ne0, ne1) }
  (* according to C: not (e0 /\ e1)  is (not e0 \/ (e0 /\ not e1)) *)
  | Cebin (Cbland, e0, e1) ->
      let ne0 = c_expr_neg e0
      and ne1 = c_expr_neg e1 in
      let e0_ne1 = { e1 with cek = Cebin (Cbland, e0, ne1) } in
      { e with cek = Cebin (Cblor, ne0, e0_ne1 ) } 
  | Celval _ -> (* condition l!=0 ; negation l==0 *)
      { e with cek = Cebin (Cbeq, e, { e with cek = Ceconst (Ccint 0) }) }
  | _ -> Log.todo_exn "negation of expression: %s" (c_expr_2str e)
(* Extraction of a function name out of a call (ptr calls non supported) *)
let c_call_name (cc: c_call): string =
  match cc.cc_fun.cek with
  | Celval { clk = Clvar v ; clt = _ } -> v.cv_name
  | _ -> Log.fatal_exn "non trivial called function expression, unsupported"

(** Basic utilities for types *)
(* Compatibility test, used for, e.g.:
 *  - verification of assignments, modulo pointer type casts
 *  - verification of index data types
 * (i.e., all pointers are considered a void* ) *)
let rec c_type_compat (t0: c_type) (t1: c_type): bool =
  let non_equal_compat = function
    | Ctptr (Some t1), Ctarray (t2, _) -> c_type_compat t1 t2
    | Ctptr (Some Ctchar), Ctstring _ -> true
    | Ctptr _, Ctptr _ -> true (* quite permissive *)
    | Ctptr _, Ctint -> true (* problem if integer is negative *)
    | Ctint, Ctptr _ -> true (* the int may overflow *)
    | Ctint, Ctarray (_, _) -> true (* the int may overflow *)
    | Ctnamed n0, Ctnamed n1 ->
        (String.compare n0.cnt_name n1.cnt_name = 0
       || c_type_compat n0.cnt_type n1.cnt_type)
    | Ctnamed n0, _ -> c_type_compat n0.cnt_type t1
    | _, Ctnamed n1 -> c_type_compat t0 n1.cnt_type
    (* valid C: int i = 'a'; char a = 123; *)
    | (Ctint | Ctchar), (Ctint | Ctchar) -> true
    (* yet unmanaged cases *)
    | Ctint, _
    | Ctchar, _
    | Ctvoid, _
    | Ctptr _, _
    | Ctstruct _, _
    | Ctunion _, _
    | Ctarray _, _
    | Ctstring _, _ -> false in
  t0 = t1 || non_equal_compat (t0, t1)
(* Read name *)
let rec c_type_read_named (t: c_type): c_type =
  match t with
  | Ctnamed ct -> c_type_read_named ct.cnt_type
  | _ -> t
(* Binary typing *)
let c_type_binary (b: c_binop) (t0: c_type) (t1: c_type): c_type =
  match b, c_type_read_named t0, c_type_read_named t1 with
  | (Cbadd | Cbsub | Cbmul | Cbmod | Cbdiv | Cbband | Cbbor),
    (Ctint | Ctchar), Ctint -> Ctint
  | (Cbland | Cblor), Ctint, Ctint -> Ctint
  | (Cbbslft | Cbbsrgh), t, _ -> t
  | (Cbeq | Cbge | Cbgt | Cble | Cblt | Cbne),
      (Ctptr _ | Ctint), (Ctptr _ | Ctint) -> Ctint
  | (Cbeq | Cbge | Cbgt | Cble | Cblt | Cbne | Cbband | Cbbor),
      (Ctint | Ctchar), (Ctint | Ctchar) -> Ctint
  | (Cbadd | Cbsub | Cbmul), Ctptr t00, Ctint -> Ctptr t00
  | (Cbadd | Cbsub | Cbmul), Ctint, Ctptr t00 -> Ctptr t00
  | (Cbadd | Cbsub | Cbmul), Ctptr t00, Ctptr t01 when t00 = t01 -> Ctptr t00
  | Cbadd, (Ctarray (t00, Some _size)), Ctint -> Ctptr (Some t00)
  | _, nt0, nt1 ->
      Log.fatal_exn "binary: %s, %s, %s"
        (c_binop_2str b) (c_type_2str nt0) (c_type_2str nt1)
(* Unary typing *)
let c_type_unary (u: c_uniop) (t0: c_type): c_type =
  match u, c_type_read_named t0 with
  | (Cuneg | Culnot | Cubnot), Ctint -> Ctint
  | (Cuneg | Culnot | Cubnot), Ctchar -> Ctchar
  | (Culnot | Cubnot), Ctptr _ -> Ctint
  | _, _ -> Log.fatal_exn "unary: %s, %s" (c_uniop_2str u) (c_type_2str t0)
(* Read a struct type and returns a field *)
let rec c_type_read_struct_field (t: c_type) (f: string): c_type =
  (* auxilliary funcitons for lists of fields (unions, structures) *)
  let extract_field (ctx: string) (l: c_agg_field list): c_type =
    let candidates = (* candidates with that field name *)
      List.filter (fun fld -> String.compare fld.caf_name f = 0) l in
    match candidates with
    | [ ] -> Log.fatal_exn "%s field %S not found" ctx f
    | [ f ] -> f.caf_typ
    | _ -> Log.fatal_exn "several entries for %s field %S" ctx f in
  match t with
  | Ctstruct (Cad_def st) -> extract_field "struct" st.cag_fields
  | Ctunion  (Cad_def su) -> extract_field "union" su.cag_fields
  | Ctnamed nt -> c_type_read_struct_field nt.cnt_type f
  | _ -> Log.fatal_exn "c_type_read_struct_field: f: '%s' not a struct: %s"
           f (c_type_2str t)
(* Read a pointer type, and returns underlying *)
let rec c_type_read_ptr (t: c_type): c_type =
  match t with
  | Ctptr (Some t) -> t
  | Ctarray (t, _size) -> t
  | Ctnamed nt -> c_type_read_ptr nt.cnt_type
  | _ -> Log.fatal_exn "not a pointer type, %s" (c_type_2str t)
(* Read a type for array cell read out *)
let c_type_read_array (t_array: c_type) (t_index: c_type): c_type =
  match t_array with
  | Ctarray (t,_) ->
      if c_type_compat t_index Ctint then t
      else Log.fatal_exn "invalid type of index, %s"
          (c_type_2str t_index)
  | Ctptr _ -> Log.fatal_exn "pointers as arrays are not handled, %s"
                 (c_type_2str t_array)
  | _ -> Log.fatal_exn "not an array type, %s" (c_type_2str t_array)

(** MemCAD string utilities *)
let parse_memcad_comstring: c_memcad_com -> c_memcad_com = function
  | Mc_comstring s ->
      read_from_string "MemCAD command string"
        Mc_parser.memcad_command Mc_lexer.token s
  | mc -> mc

(** Iteration function over types in the program *)
let c_prog_apply_type_op (f: c_type -> c_type) (p: c_prog): c_prog =
  let do_c_type = f in
  let do_c_agg_field (f: c_agg_field): c_agg_field =
    { f with caf_typ = do_c_type f.caf_typ } in
  let do_c_aggregate (a: c_aggregate): c_aggregate =
    { a with cag_fields = List.map do_c_agg_field a.cag_fields } in
  let do_c_var (v: c_var): c_var = { v with cv_type = do_c_type v.cv_type } in
  let rec do_c_exprk (e: c_exprk): c_exprk =
    match e with
    | Ceconst _ -> e
    | Celval l -> Celval (do_c_lval l)
    | Ceaddrof l -> Ceaddrof (do_c_lval l)
    | Ceuni (o0, e1) -> Ceuni (o0, do_c_expr e1)
    | Cebin (o0, e1, e2) -> Cebin (o0, do_c_expr e1, do_c_expr e2)
  and do_c_expr (e: c_expr): c_expr = { cek = do_c_exprk e.cek ;
                                        cet = do_c_type e.cet }
  and do_c_lvalk (l: c_lvalk): c_lvalk =
    match l with
    | Clvar v -> Clvar (do_c_var v)
    | Clfield (l0, s) -> Clfield (do_c_lval l0, s)
    | Clindex (l0, e) -> Clindex (do_c_lval l0, do_c_expr e)
    | Clderef e -> Clderef (do_c_expr e)
  and do_c_lval (l: c_lval): c_lval = { clk = do_c_lvalk l.clk ;
                                        clt = do_c_type l.clt } in
  let do_c_memcad_iparam (ip: c_memcad_iparam): c_memcad_iparam =
    match ip with
    | Cmp_const _ -> ip
    | Cmp_lval l -> Cmp_lval (do_c_lval l) in
  let do_c_memcad_setvar (setv: c_memcad_setvar): c_memcad_setvar = setv in
  let do_c_memcad_iparams (ips: c_memcad_iparams): c_memcad_iparams =
    { mc_pptr = List.map do_c_memcad_iparam ips.mc_pptr;
      mc_pint = List.map do_c_memcad_iparam ips.mc_pint;
      mc_pset = ips.mc_pset } in
  let do_c_memcad_setexpr (se: c_memcad_setexpr): c_memcad_setexpr =
    match se with
    | Cmp_subset (l, r) ->
        Cmp_subset (do_c_memcad_setvar l, do_c_memcad_setvar r)
    | Cmp_mem (m, r) ->
        Cmp_mem (do_c_lval m, do_c_memcad_setvar r)
    | Cmp_empty l ->
        Cmp_empty (do_c_memcad_setvar l)
    | Cmp_euplus (l, m, r) ->
        Cmp_euplus (do_c_memcad_setvar l, do_c_lval m, do_c_memcad_setvar r) in
  let do_c_memcad_com (com: c_memcad_com): c_memcad_com =
    let preprocess_num_exprs num_exprs =
      List.map (fun (op, l, a) ->
          (op, do_c_lval l, do_c_memcad_iparam a)
        ) num_exprs in
    let preprocess_set_exprs set_exprs =
      List.map do_c_memcad_setexpr set_exprs in
    let preprocess_set_vars set_vars =
      List.map do_c_memcad_setvar set_vars in
    let preprocess_c_vars c_vars =
      List.map do_c_var c_vars in
    match com with
    | Mc_assume num_exprs ->
        Mc_assume (preprocess_num_exprs num_exprs)
    | Mc_add_inductive (l, s, a) ->
        Mc_add_inductive (do_c_lval l, s, Option.map do_c_memcad_iparams a)
    | Mc_add_segment (l, s, a, le, se, ae) ->
        Mc_add_segment (do_c_lval l, s, Option.map do_c_memcad_iparams a,
                        do_c_lval le, se, Option.map do_c_memcad_iparams ae)
    | Mc_check_inductive (l, s, a) ->
        Mc_check_inductive (do_c_lval l, s, Option.map do_c_memcad_iparams a)
    | Mc_check_segment (l, s, a, le, se, ae) ->
        Mc_check_segment (do_c_lval l, s, Option.map do_c_memcad_iparams a,
                          do_c_lval le, se, Option.map do_c_memcad_iparams ae)
    | Mc_unfold l -> Mc_unfold (do_c_lval l)
    | Mc_unfold_bseg l -> Mc_unfold_bseg (do_c_lval l)
    | Mc_sel_merge l -> Mc_sel_merge (preprocess_c_vars l)
    | Mc_force_live l -> Mc_force_live (preprocess_c_vars l)
    | Mc_reduce_localize l -> Mc_reduce_localize (do_c_lval l)
    | Mc_output_ext _
    | Mc_check_bottomness _
    | Mc_unroll _
    | Mc_merge
    | Mc_kill_flow
    | Mc_reduce_eager
    | Mc_output_stdout
    | Mc_array_check
    | Mc_array_assume
    | Mc_comstring _ -> com
    | Mc_add_setexprs l -> Mc_add_setexprs (preprocess_set_exprs l)
    | Mc_check_setexprs l -> Mc_check_setexprs (preprocess_set_exprs l)
    | Mc_decl_setvars l -> Mc_decl_setvars (preprocess_set_vars l) in
  let do_c_call (c: c_call): c_call =
    { cc_fun  = do_c_expr c.cc_fun;
      cc_args = List.map do_c_expr c.cc_args } in
  let rec do_c_statk (s: c_statk): c_statk =
    match s with
    | Csdecl v -> Csdecl (do_c_var v)
    | Cspcall c -> Cspcall (do_c_call c)
    | Csfcall (l, c) -> Csfcall (do_c_lval l, do_c_call c)
    | Csassign (l, e) -> Csassign (do_c_lval l, do_c_expr e)
    | Csblock b -> Csblock (do_c_block b)
    | Csif (e0, b1, b2) -> Csif (do_c_expr e0, do_c_block b1, do_c_block b2)
    | Cswhile (e0, b1, o) -> Cswhile (do_c_expr e0, do_c_block b1, o)
    | Csreturn (Some e) -> Csreturn (Some (do_c_expr e))
    | Csreturn None
    | Csbreak | Cscontinue | Csexit -> s
    | Cs_memcad mc -> Cs_memcad (do_c_memcad_com mc)
    | Csassert e -> Csassert (do_c_expr e)
    | Csalloc (l, e) -> Csalloc (do_c_lval l, do_c_expr e)
    | Csfree l -> Csfree (do_c_lval l)
  and do_c_stat (s: c_stat): c_stat = { s with csk = do_c_statk s.csk }
  and do_c_block (b: c_block): c_block = List.map do_c_stat b in
  let do_c_fun (f: c_fun): c_fun =
    { f with
      cf_type = do_c_type f.cf_type ;
      cf_args = List.map do_c_var f.cf_args ;
      cf_body = do_c_block f.cf_body } in
  { cp_vars  = StringMap.map do_c_var p.cp_vars ;
    cp_funs  = StringMap.map do_c_fun p.cp_funs ;
    cp_types = StringMap.map do_c_type p.cp_types ;
    cp_aggs  = StringMap.map do_c_aggregate p.cp_aggs }

(** Translations between C and abstract domain syntax *)
let tr_c_type: c_type -> typ =
  let rec aux_type (loop: bool) (seen: StringSet.t) (t: c_type): typ =
    match t with
    | Ctvoid -> Tvoid
    | Ctint -> Tint (4, Tsigned)
    | Ctchar -> Tint (1, Tunsigned)
    | Ctstruct (Cad_named _)
    | Ctunion  (Cad_named _) -> Tunk
    | Ctnamed n ->
        begin
          if StringSet.mem n.cnt_name seen then
            Tnamed n.cnt_name
          else
            try Ast_utils.tnamed_find n.cnt_name
            with Not_found -> Tunk (* circularity due to pointers *)
        end
    | Ctstruct (Cad_def s) ->
        let sfields =
          List.map
            (fun fld ->
              { tsf_name = fld.caf_name;
                tsf_off  = fld.caf_off;
                tsf_size = fld.caf_size;
                tsf_typ  = aux_type loop seen fld.caf_typ }
            ) s.cag_fields in
        Tstruct { ts_align  = s.cag_align;
                  ts_size   = s.cag_size;
                  ts_fields = sfields }
    | Ctptr (Some (Ctnamed n)) ->
        if loop then Tptr (Some (Tnamed n.cnt_name))
        else Tptr (Some (aux_type loop seen (Ctnamed n)))
    | Ctptr t -> Tptr (Option.map (aux_type loop seen) t)
    | Ctarray (t, Some n) -> Tarray (aux_type loop seen t, n)
    | Ctarray (t, None)   -> Tptr (Some (aux_type loop seen t)) (* ptr type *)
    | Ctstring n -> Tstring n
    | Ctunion (Cad_def u) ->
        let ufields =
          List.map
            (fun fld ->
              { tuf_name = fld.caf_name;
                tuf_size = fld.caf_size;
                tuf_typ  = aux_type loop seen fld.caf_typ }
            ) u.cag_fields in
        Tunion { tu_align  = u.cag_align;
                 tu_size   = u.cag_size;
                 tu_fields = ufields } in
  aux_type false StringSet.empty
let tr_c_var (v: c_var): var =
  { v_name = v.cv_name ;
    v_id   = v.cv_uid ;
    v_typ  = tr_c_type v.cv_type }
let tr_c_const (c: c_const): const =
  match c with
  | Ccint i -> Cint i
  | Ccchar c -> Cchar c
  | Ccstring s -> Cstring s
  | Ccnull -> Cint 0
let tr_c_field (t: c_type) (fld: string): field =
  let ooff =
    match tr_c_type t with
    | Tstruct t -> Some (Ast_utils.find_field t fld).tsf_off
    | Tunion tu -> Some 0
    | _ -> Log.fatal_exn "field in a non pack type" in
  { f_name = fld ;
    f_off  = ooff }
let rec tr_c_exprk (e: c_exprk): var expr =
  match e with
  | Ceconst c -> Ecst (tr_c_const c)
  | Celval l ->
      begin
        match l.clk with
        | Clvar v -> if v.cv_volatile then Erand else Elval (tr_c_lval l)
        | _ -> Elval (tr_c_lval l)
      end
  | Ceuni (Cuneg , e0)     -> Euni (Uneg , tr_c_expr e0)
  | Ceuni (Culnot, e0)     -> Euni (Unot , tr_c_expr e0)
  | Ceuni (Cubnot, e0)     -> Euni (Ubnot, tr_c_expr e0)
  | Cebin (Cbadd , e0, e1) -> Ebin (Badd, tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cbmul , e0, e1) -> Ebin (Bmul, tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cbsub , e0, e1) -> Ebin (Bsub, tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cbmod , e0, e1) -> Ebin (Bmod, tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cbdiv , e0, e1) -> Ebin (Bdiv, tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cbge  , e0, e1) -> Ebin (Bge , tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cbgt  , e0, e1) -> Ebin (Bgt , tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cble  , e0, e1) -> Ebin (Bge , tr_c_expr e1, tr_c_expr e0)
  | Cebin (Cblt  , e0, e1) -> Ebin (Bgt , tr_c_expr e1, tr_c_expr e0)
  | Cebin (Cbeq  , e0, e1) -> Ebin (Beq , tr_c_expr e1, tr_c_expr e0)
  | Cebin (Cbne  , e0, e1) -> Ebin (Bne , tr_c_expr e1, tr_c_expr e0)
  | Cebin (Cbland, e0, e1) -> Ebin (Band, tr_c_expr e0, tr_c_expr e1)
  | Cebin (Cblor , e0, e1) -> 
      (* accodring to c: e0 \/ e1 is : e0 \/ (not e0 /\ e1) *)
      let ne0 = c_expr_neg e0 in
      let ne0_e1 =  { e1 with cek = Cebin (Cbland, ne0, e1) } in
      Ebin (Bor , tr_c_expr e0, tr_c_expr ne0_e1)
  | Cebin (Cbband, e0, e1) -> Erand
  | Cebin (Cbbor , e0, e1) -> Erand
  | Cebin (Cbbslft, e0, e1) -> Erand
  | Cebin (Cbbsrgh, e0, e1) -> Erand
  | Ceaddrof l -> EAddrOf (tr_c_lval l)
and tr_c_expr (e: c_expr): var texpr  =
  tr_c_exprk e.cek, tr_c_type e.cet
and tr_c_lvalk (l: c_lvalk): var lval =
  match l with
  | Clvar v -> Lvar (tr_c_var v)
  | Clfield (l0, fld) -> Lfield (tr_c_lval l0, tr_c_field l0.clt fld)
  | Clderef e0 -> Lderef (tr_c_expr e0)
  | Clindex (l0, e0) -> Lindex (tr_c_lval l0, tr_c_expr e0)
and tr_c_lval (l: c_lval): var tlval =
  tr_c_lvalk l.clk, tr_c_type l.clt

(**  Translations between C set expression and abstract domain syntax *)
let tr_c_setvar (l: c_memcad_setvar): setvar =
  { s_name = l.mc_setvar_name;
    s_uid  = l.mc_setvar_uid;
    s_root = true; }
let tr_c_setexpr (l: c_memcad_setexpr): var tlval setprop =
  match l with
  | Cmp_subset (l, r) -> Sp_sub (tr_c_setvar l, tr_c_setvar r)
  | Cmp_mem (c, r) -> Sp_mem (tr_c_lval c, tr_c_setvar r)
  | Cmp_empty l -> Sp_emp (tr_c_setvar l)
  | Cmp_euplus (l, c, r) ->
      Sp_euplus (tr_c_setvar l, tr_c_lval c, tr_c_setvar r)
