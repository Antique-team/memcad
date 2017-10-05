(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: transform.ml
 **       transforming the Clang AST into the MemCAD AST
 ** Pippijn Van Steenhoeven and Francois Berenger, 2014/08/21 *)
open C_sig
open Clang
open Ast
open Data_structures
open Util


module Log = 
  Logger.Make(struct let section = "transfo_" and level = Log_level.DEBUG end)


(***********************************************************************
 * Sizeof/alignof queries
 ***********************************************************************)

let sizeof (clang: Clang.Api.clang) (ctyp: Clang.Ast.ctyp): int =
  Int64.to_int Api.(request clang @@ SizeofType ctyp.t_cref)

let alignof (clang: Clang.Api.clang) (ctyp: Clang.Ast.ctyp): int =
  Api.(request clang @@ AlignofType ctyp.t_cref)

(***********************************************************************
 * Builtin types
 ***********************************************************************)

let c_type_of_builtin_type (btt: Clang.AstBridge.builtin_type): c_type =
  (* FBR: should use signed or unsigned types with proper size *)
  match btt with
  | BT_Void -> Ctvoid
  | BT_Char16
  | BT_Char32
  | BT_Short
  | BT_Long
  | BT_LongLong
  | BT_Int128
  | BT_UShort
  | BT_ULong
  | BT_ULongLong
  | BT_UInt128
  | BT_UInt
  | BT_Int -> Ctint
  | BT_Bool
  | BT_SChar
  | BT_UChar
  | BT_Char_S
  | BT_Char_U -> Ctchar
  | _ -> Ctint

(***********************************************************************
 * Aggregates (struct/union)
 ***********************************************************************)

let make_def_aggregate (agg: C_sig.c_aggregate) (ttk: Clang.Ast.tag_type_kind)
  : C_sig.c_type =
  match ttk with
  | TTK_Struct -> Ctstruct (Cad_def agg)
  | TTK_Union  -> Ctunion  (Cad_def agg)
  | _ -> Log.fatal_exn "make_def_aggregate: Unhandled tag type kind"

let compute_offset kind (off: int) (align: int): int =
  if kind = TTK_Union then 0
  else ((off + align - 1) / align) * align

(* detect if any global var. initialization was unused *)
let saw_global_init = ref false
let saw_main = ref false

type env = { prog : c_prog ;
             ns : string ;
             (* management of vars declared and initialized at file scope *)
             delayed_init_vars : StringSet.t ; (* var. names *)
             (* decls in reverse order of appearance (because in a list) *)
             delayed_init_decls : Clang.Ast.decl list }

let add_type (name: string) (ty: C_sig.c_type) (env: env): env =
  match name with
  | "__int128_t" | "__uint128_t" | "__builtin_va_list" ->
    env (* we ignore clang-generated type names *)
  | name ->
    try
      let name = env.ns ^ name in
      let prev_type = StringMap.find name env.prog.cp_types in
      let is_a_defined_struct = function
        | Ctstruct (Cad_def _c_aggr) -> true
        | _ -> false in
      if (prev_type <> ty) || not (is_a_defined_struct ty) then
        Log.fatal_exn
          "add_type: name '%s' already in map env.prog.cp_types w/ type: %s"
          name (C_utils.c_type_2stri "" ty)
      else (* struct without a typedef *)
        env
    with Not_found -> (* yet unseen type *)
      { env with prog = {
           env.prog with cp_types = StringMap.add name ty env.prog.cp_types }
      }

let nb_anon_structs = ref 0

(* for strucs declared without a typedef, we can add their type to the env.
   only when we see them being used *)
let add_struct_type (ty: Clang.Ast.tloc) (env: env)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t): env =
  match ty.tl with
    | ElaboratedTypeLoc { tl = RecordTypeLoc (_, name2); tl_type }
    | PointerTypeLoc { tl = ElaboratedTypeLoc
                           { tl = RecordTypeLoc (_, name2); tl_type } }
    | ConstantArrayTypeLoc ({ tl = ElaboratedTypeLoc
                           { tl = RecordTypeLoc (_, name2); tl_type } },
                            _)
    | ConstantArrayTypeLoc ({ tl = PointerTypeLoc
                                  { tl = ElaboratedTypeLoc
                                        { tl = RecordTypeLoc (_, name2); tl_type } } },
                            _) ->
      (* struct w/o typedef, or pointer to that, or table of that or
       * table of pointer of that *)
      let c_type = DenseIntMap.find tl_type.t_self c_types in
      let name2 =
        if name2 <> "" then name2
        else (* no typedef and no struct name:
                we assign it a unique temp. name which cannot appear
                in valid C source code *)
          let res = Printf.sprintf "%%mc_transfo_anon_struct_%d" !nb_anon_structs in
          incr nb_anon_structs;
          res
      in
      add_type name2 c_type env
    | _ -> env

(* to unfold types up to a given depth *)
let (seen_times: int StringMap.t ref) = ref StringMap.empty

let rec c_agg_fields_of_decls
    (clang: Clang.Api.clang)
    ((cache, seen): C_sig.c_type StringMap.t *
                    Clang.Ast.ctyp Util.DenseIntMap.key StringMap.t)
    kind
    (decls: decl list)
  : C_sig.c_type StringMap.t *
    Clang.Ast.ctyp Util.DenseIntMap.key StringMap.t *
    C_sig.c_agg_field list =
  let rec loop off (cache, seen, fields) declarations = match declarations with
    | [] -> (cache, seen, List.rev fields)
    | { d = RecordDecl (_ttk, name1, Some members, _) }
      :: { d = FieldDecl {
          fd_type = {
            tl = ElaboratedTypeLoc {
                tl = RecordTypeLoc (kind, name2);
                tl_type;
              }
          };
          fd_name = name;
          fd_bitw = bitwidth;
          fd_init = init;
        } } :: tl when name1 = name2 ->
      if init <> None then Log.fatal_exn "Member initialisers not implemented";
      let size  = sizeof  clang tl_type in
      let align = alignof clang tl_type in
      let cache, seen, cag_fields =
        c_agg_fields_of_decls clang (cache, seen) kind members
      in
      let agg = { cag_name   = if name1 = "" then None else Some name1;
                  cag_align  = align;
                  cag_size   = size;
                  cag_fields }
      in
      (* offset for the current field *)
      let off = compute_offset kind off align in
      let field = { caf_typ  = make_def_aggregate agg kind;
                    caf_off  = off;
                    caf_size = size;
                    caf_name = name }
      in
      (* offset for the next field *)
      let off = off + size in
      loop off (cache, seen, field :: fields) tl
    | { d = RecordDecl (_ttk, _name, None (* members *), _) } :: tl ->
      (* this is a forward declaration introduced by clang, just ignore it
         as it is not a field *)
      loop off (cache, seen, fields) tl
    | { d = FieldDecl { fd_type = ty;
                        fd_name = name;
                        fd_bitw = bitwidth;
                        fd_init = init;
                        fd_index } } :: tl ->
      if bitwidth <> None then Log.fatal_exn "Bit fields not implemented";
      if init <> None then Log.fatal_exn "Member initialisers not implemented";
      let size  = sizeof  clang ty.tl_type in
      let align = alignof clang ty.tl_type in
      (* offset for the current field *)
      let off = compute_offset kind off align in
      let (cache, seen), ty = mctype_of_ctyp clang (cache, seen) ty.tl_type in
      let field = { caf_typ  = ty;
                    caf_off  = off;
                    caf_size = size;
                    caf_name = name }
      in
      (* offset for the next field *)
      let off = off + size in
      loop off (cache, seen, field :: fields) tl
   | { d } :: tl ->
       Log.fatal_exn "%s\nOnly FieldDecls allowed within RecordDecl" (Pp.string_of_decl_ d)
  in
  loop 0 (cache, seen, []) decls

(***********************************************************************
 * Main recursive entry point for type translation
 ***********************************************************************)

(* MemCAD type of clang type *)
and mctype_of_ctyp
    (clang: Clang.Api.clang)
    ((cache, seen): C_sig.c_type StringMap.t *
                    Clang.Ast.ctyp Util.DenseIntMap.key StringMap.t)
    (ctyp: Clang.Ast.ctyp)
  : (C_sig.c_type StringMap.t *
     Clang.Ast.ctyp Util.DenseIntMap.key StringMap.t) *
    C_sig.c_type =
  match ctyp.t with
  | BuiltinType bt -> ((cache, seen), c_type_of_builtin_type bt)
  | ConstantArrayType (memty, size) ->
    let (cache, seen), memty = mctype_of_ctyp clang (cache, seen) memty in
    ((cache, seen), Ctarray (memty, Some size))
  | IncompleteArrayType memty ->
    let (cache, seen), memty = mctype_of_ctyp clang (cache, seen) memty in
    ((cache, seen), Ctarray (memty, None))
  | TypedefType name ->
    if name = "" then Log.fatal_exn "mctype_of_ctyp: empty name in TypedefType";
    begin
      try
        let decl = Api.(request clang @@ DeclOfType ctyp.t_cref) in
        let (cache, seen), c_type =
          let tloc = Query.underlying_type_of_typedef_decl decl.d in
          mctype_of_ctyp clang (cache, seen) tloc.tl_type
        in
        ((cache, seen), Ctnamed { cnt_name = name; cnt_type = c_type })
      with Api.E (Api.E_Failure msg) ->
        Log.warn "typedef name: %s: %s" name msg;
        ((cache, seen), Ctnamed { cnt_name = name; cnt_type = Ctvoid })
    end
  | ElaboratedType ty -> mctype_of_ctyp clang (cache, seen) ty
  | EnumType name ->
    ((cache, seen), c_type_of_builtin_type BT_Int)
  | RecordType (kind, name) ->
    let cnt_name = string_of_int (ctyp.t_self :> int) in
    let already_seen = StringMap.mem cnt_name seen in
    let seen =
      if already_seen then
        seen
      else
        begin
          if name <> "" then
            seen_times := StringMap.add name 0 !seen_times;
          StringMap.add cnt_name ctyp.t_self seen
        end
    in
    if name <> "" then
      begin
        let count = StringMap.find name !seen_times in
        seen_times := StringMap.update name (count + 1) !seen_times
      end;
    if already_seen && name <> "" &&
       (StringMap.find name !seen_times) > !Flags.type_unfolds then begin
      try ((cache, seen), StringMap.find cnt_name cache)
      with Not_found ->
        ((cache, seen), Ctnamed { cnt_name = name; cnt_type = Ctvoid })
    end else
      (try
        let decl = Api.(request clang @@ DeclOfType ctyp.t_cref) in
        let cache, seen, cag_fields =
          let members = Query.fields_of_record_decl decl.d in
          c_agg_fields_of_decls clang (cache, seen) kind members
        in
        let c_type =
          make_def_aggregate {
            cag_name   = if name = "" then None else Some name;
            cag_align  = alignof clang ctyp;
            cag_size   = sizeof  clang ctyp;
            cag_fields;
          } kind
        in
        let cache = StringMap.add cnt_name c_type cache in
        ((cache, seen), c_type)
      with Api.E (Api.E_Failure msg) ->
        let c_type =
          Ctnamed { cnt_name = "struct " ^ name; cnt_type = Ctvoid }
        in
        let cache = StringMap.add cnt_name c_type cache in
        Log.warn "tag type name: %s: %s" name msg;
        ((cache, seen), c_type)
      )
  | ParenType inner -> mctype_of_ctyp clang (cache, seen) inner
  | PointerType { t = FunctionNoProtoType res
                    | FunctionProtoType (res, _) }
  | FunctionNoProtoType res
  | FunctionProtoType (res, _) ->
    mctype_of_ctyp clang (cache, seen) res
  | PointerType pointee ->
    let (cache, seen), pointee = mctype_of_ctyp clang (cache, seen) pointee in
    ((cache, seen), Ctptr (Some (pointee)))
  | DecayedType (decayed, _original) ->
    mctype_of_ctyp clang (cache, seen) decayed
  | TypeOfExprType _ -> Log.fatal_exn "TypeOfExprType"
  | TypeOfType _ -> Log.fatal_exn "TypeOfType"
  | VariableArrayType _ -> Log.fatal_exn "VariableArrayType"
  | ty -> Log.fatal_exn "%s" (Pp.string_of_ctyp_ ty)

(***********************************************************************
 * Mapping the type map (array) from clang to memcad types
 ***********************************************************************)

let rec resolve_c_type
    (seen: Clang.Ast.ctyp Util.DenseIntMap.key StringMap.t)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (c_type: C_sig.c_type): unit =
  match c_type with
  | Ctint
  | Ctchar
  | Ctvoid
  | Ctptr None
  | Ctstring _
  (* a named aggregate (struct or union) without a definition cannot
     be resolved since it has no fields.
     This is OK since an aggregate with the same name but with a definition
     exists somewhere and will be resolved *)
  | Ctstruct (Cad_named _)
  | Ctunion  (Cad_named _) -> ()
  | Ctnamed ({ cnt_type = Ctnamed { cnt_name; cnt_type = Ctptr None } }
             as c_named) ->
    let key = StringMap.find cnt_name seen in
    c_named.cnt_type <- DenseIntMap.find key c_types
  | Ctnamed c_named -> resolve_c_type seen c_types c_named.cnt_type
  | Ctstruct (Cad_def aggr)
  | Ctunion (Cad_def aggr) ->
    List.iter
      (fun cf -> resolve_c_type seen c_types cf.caf_typ)
      aggr.cag_fields
  | Ctptr (Some ty)
  | Ctarray (ty, _) -> resolve_c_type seen c_types ty

let map_types
    (clang: Clang.Api.clang)
    (types: (Clang.Ast.ctyp, Clang.Ast.ctyp) Util.DenseIntMap.t)
  : (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t =
  let ((cache, seen), c_types) =
    DenseIntMap.mapvf
      (fun _i ctyp seen -> mctype_of_ctyp clang seen ctyp)
      types
      (StringMap.empty, StringMap.empty)
  in
  DenseIntMap.iter
    (fun _ c_type -> resolve_c_type seen c_types c_type)
    c_types;
  (* DenseIntMap.iter *)
  (*   (fun key c_type -> *)
  (*      Format.printf "%d: %a\n" *)
  (*        (key : ctyp DenseIntMap.key :> int) *)
  (*        Show_c_type.format c_type) *)
  (*   c_types; *)
  c_types

let start_line (clang: Clang.Api.clang) (loc: Clang.Ast.sloc): int =
  Api.(request clang @@ PresumedLoc loc.loc_s).Sloc.loc_line

let c_var_of_c_fun (func: c_fun): c_var =
  { cv_name     = func.cf_name ;
    cv_uid      = func.cf_uid  ;
    cv_type     = func.cf_type ;
    cv_volatile = false        }

let lookup_var (clang: Clang.Api.clang) (sloc: Clang.Ast.sloc)
    (env: env) (decl_env: C_sig.c_var StringMap.t) (name: StringMap.key)
  : C_sig.c_var =
  try StringMap.find name decl_env
  with Not_found ->
    try StringMap.find name env.prog.cp_vars
    with Not_found ->
      try
        let func = StringMap.find name env.prog.cp_funs in
        c_var_of_c_fun func
      with Not_found ->
        let line = start_line clang sloc in
        Log.fatal_exn "lookup failed for var %s at line %d:\n%s"
          name line (Lib.get_line !Flags.analyzed_file line)

let add_fun (curr_fun: C_sig.c_fun) (env: env): env =
  let name = env.ns ^ curr_fun.cf_name in
  if StringMap.mem name env.prog.cp_funs then
    (* it is maybe OK to replace a function without definition
       with a function of the same name once we have its definition *)
    let prev_fun = StringMap.find name env.prog.cp_funs in
    if (prev_fun.cf_body <> []) || (curr_fun.cf_body = []) then
      begin
        Log.warn "add_fun: name already in map env.prog.cp_funs: %s" name;
        env
      end
    else
      let m =
        StringMap.add name curr_fun (StringMap.remove name env.prog.cp_funs)
      in
      { env with prog = { env.prog with cp_funs = m } }
  else
    let m = StringMap.add name curr_fun env.prog.cp_funs in
    { env with prog = { env.prog with cp_funs = m } }

let add_var (var: C_sig.c_var) (env: env): env =
  let name = env.ns ^ var.cv_name in
  if StringMap.mem name env.prog.cp_vars then
    Log.fatal_exn "add_var: name %s already in map env.prog.cp_vars" name;
  { env with prog = {
       env.prog with cp_vars = StringMap.add name var env.prog.cp_vars } }

(* add a declaration with initialization at file scope to
   the map of such declarations *)
let add_delayed_init (decl_w_init: Clang.Ast.decl) (env: env): env =
  saw_global_init := true;
  match decl_w_init with
    | { d = VarDecl (ty, name, Some init) } ->
      let name = env.ns ^ name in
      if StringSet.mem name env.delayed_init_vars then
        Log.fatal_exn
          "add_delayed_init: name %s already in map env.delayed_inits" name
      else
        let delayed_init_vars' = StringSet.add name env.delayed_init_vars in
        let delayed_init_decls' = decl_w_init :: env.delayed_init_decls in
        { env with delayed_init_vars  = delayed_init_vars'  ;
                   delayed_init_decls = delayed_init_decls' }
    | _ -> Log.fatal_exn "add_delayed_init: unsupported decl: %s"
             (Pp.string_of_decl decl_w_init)

let collect_delayed_init_stmts (env: env): Clang.Ast.stmt list =
  List.fold_left (* reverts the list env.delayed_init_decls on purpose *)
    (fun acc decl -> match decl with
       | { d = VarDecl (ty, name, Some init) } ->
         let init_stmt = {
           s = ExprStmt {
               e = BinaryOperator (
                   BO_Assign,
                   { e = DeclRefExpr name;
                     e_sloc = decl.d_sloc;
                     e_type = ty.tl_type;
                     e_cref = Ref.null },
                   init);
               e_sloc = decl.d_sloc;
               e_type = init.e_type;
               e_cref = Ref.null };
           s_sloc = init.e_sloc;
           s_cref = Ref.null }
         in
         init_stmt :: acc
       | _ -> assert(false);
    )
    [] env.delayed_init_decls

let c_binop_of_binary_operator (op: Clang.Ast.binary_operator) clang sloc
  : C_sig.c_binop =
  match op with
  | BO_EQ -> Cbeq
  | BO_NE -> Cbne
  | BO_GE -> Cbge
  | BO_GT -> Cbgt
  | BO_LE -> Cble
  | BO_LT -> Cblt
  | BO_Add -> Cbadd
  | BO_Sub -> Cbsub
  | BO_Mul -> Cbmul
  | BO_Div -> Cbdiv
  | BO_LAnd -> Cbland
  | BO_LOr -> Cblor
  | BO_Rem -> Cbmod
  | BO_And -> Cbband
  | BO_Or -> Cbbor
  | BO_Shl -> Cbbslft
  | BO_Shr -> Cbbsrgh
  | _ ->
    let line = start_line clang sloc in
    Log.fatal_exn "unsupported binop %s at line %d\n%s"
      (Pp.string_of_binary_op op)
      line
      (Lib.get_line !Flags.analyzed_file line)

let c_uniop_of_unary_operator (op: Clang.Ast.unary_operator): C_sig.c_uniop =
  match op with
  | UO_Minus -> Cuneg
  | UO_LNot  -> Culnot
  | UO_Not   -> Cubnot
  | op -> Log.fatal_exn "unsupported uniop: %s" (Pp.string_of_unary_op op)

let c_var_of_parm_decl
    (env: env)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (parm_decl: Clang.Ast.decl): env * C_sig.c_var =
  match parm_decl with
  | { d = ParmVarDecl (ty, name) } ->
    let env = add_struct_type ty env c_types in
    (env,
     { cv_name     = name ;
       cv_uid      = -1 ;
       cv_type     = DenseIntMap.find ty.tl_type.t_self c_types ;
       cv_volatile = Query.is_volatile_tloc ty.tl })
  | _ -> Log.fatal_exn "only ParmVarDecls allowed in function argument list"

let create_c_fun_forward_decl
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (ty: Clang.Ast.tloc)
    (name: string): env * C_sig.c_fun =
  (* Create the signature of the function (without body) first,
     so that name lookups within the (eventual) body work for the
     currently processed function. *)
  let env, cf_args =
    List.fold_right (* don't reverse args' order ... *)
      (fun pd (env, acc) ->
         let env, var = c_var_of_parm_decl env c_types pd in
         (env, var :: acc))
      (Query.args_of_tloc ty.tl)
      (env, []) in
  let ret_type = Query.return_type_of_tloc ty.tl in
  let c_fun = { cf_type = DenseIntMap.find ret_type.tl_type.t_self c_types;
                cf_uid  = -1;
                cf_name = name;
                cf_args = cf_args;
                cf_body = [] } in
  (env, c_fun)

type env_or_loc_cvar = Env of (env * C_sig.c_fun)
                     | Loc_cvar of (int * C_sig.c_var)

let c_decl_of_decl
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    ({ d_sloc; d }: Clang.Ast.decl)
  : env_or_loc_cvar =
  let line = start_line clang d_sloc in
  match d with
  | VarDecl (ty, name, init) ->
    (match init with
     | None -> ()
     | Some x -> Log.fatal_exn "Unsupported: initialiser for %s: %s\n
                            (transform SplitInitialisers not applied?)"
                   name (Pp.string_of_expr x)
    );
    Loc_cvar (line, { cv_name     = name;
                      cv_uid      = -1;
                      cv_type     = DenseIntMap.find ty.tl_type.t_self c_types;
                      cv_volatile = Query.is_volatile_tloc ty.tl })
  | FunctionDecl (ty, DN_Identifier name, None) ->
    (* local forward function declaration *)
    Env (create_c_fun_forward_decl clang c_types env ty name)
  | FunctionDecl (_ty, DN_Identifier name, Some _body) ->
    Log.fatal_exn "local function declaration of %s at line %d" name line
  | EmptyDecl ->
    Log.fatal_exn "empty declaration within function body at line %d" line
  | TypedefDecl (ty, name) ->
    Log.fatal_exn "local typedefs are not supported by memcad AST; line %d"
             line
  | EnumDecl (name, enumerators) ->
    Log.fatal_exn "local enums are not supported by memcad AST; line %d"
             line
  | RecordDecl (kind, name, members, _) ->
    Log.fatal_exn "local %ss are not supported by memcad AST; line %d"
             (Pp.string_of_tag_type_kind kind) line
  | EnumConstantDecl _ ->
    Log.fatal_exn "EnumConstantDecl found in function at line %d" line
  | FieldDecl        _ ->
    Log.fatal_exn "FieldDecl found in function at line %d" line
  | ParmVarDecl      _ ->
    Log.fatal_exn "ParmVarDecl found in function at line %d" line
  | TranslationUnitDecl _ ->
    Log.fatal_exn "TranslationUnitDecl found in function at line %d" line
  | decl ->
    Log.fatal_exn "%s at line %d" (Pp.string_of_decl_ decl) line

let rec c_lvalk_of_expr
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (expr: Clang.Ast.expr): C_sig.c_lvalk =
  let line = start_line clang expr.e_sloc in
  let error s =
    Log.fatal_exn "%s at line %d\n%s\n"
      s line (Lib.get_line !Flags.analyzed_file line) in
  match expr.e with
  | DeclRefExpr name -> Clvar (lookup_var clang expr.e_sloc env decl_env name)
  | MemberExpr (({ e_type = ty } as base), member, is_arrow) ->
    (* print_endline (Pp.string_of_ctyp ty); *)
    let base =
      if is_arrow then
        { clk = Clderef (c_expr_of_expr clang c_types env decl_env base);
          clt = DenseIntMap.find ty.t_self c_types }
      else
        c_lval_of_expr clang c_types env decl_env base
    in
    Clfield (base, member)
  | ArraySubscriptExpr (base, index) ->
    Clindex (c_lval_of_expr clang c_types env decl_env base,
             c_expr_of_expr clang c_types env decl_env index)
  | UnaryOperator (UO_Deref, expr) ->
    Clderef (c_expr_of_expr clang c_types env decl_env expr)
  | IntegerLiteral _ -> error "c_lvalk_of_expr: IntegerLiteral"
  | CharacterLiteral _ -> error "c_lvalk_of_expr: CharacterLiteral"
  | FloatingLiteral _ -> error "c_lvalk_of_expr: FloatingLiteral"
  | StringLiteral _ -> error "c_lvalk_of_expr: StringLiteral"
  | BinaryOperator _ -> error "c_lvalk_of_expr: BinaryOperator"
  | UnaryOperator _ -> error "c_lvalk_of_expr: UnaryOperator"
  | PredefinedExpr _ -> error "c_lvalk_of_expr: PredefinedExpr"
  | ImplicitCastExpr _ -> error "c_lvalk_of_expr: ImplicitCastExpr"
  | CStyleCastExpr _ -> error "c_lvalk_of_expr: CStyleCastExpr"
  | CompoundLiteralExpr _ -> error "c_lvalk_of_expr: CompoundLiteralExpr"
  | ParenExpr _ -> error "c_lvalk_of_expr: ParenExpr"
  | VAArgExpr _ -> error "c_lvalk_of_expr: VAArgExpr"
  | CallExpr _ -> error "c_lvalk_of_expr: CallExpr"
  | ConditionalOperator _ -> error "c_lvalk_of_expr: ConditionalOperator"
  | DesignatedInitExpr _ -> error "c_lvalk_of_expr: DesignatedInitExpr"
  | InitListExpr _ -> error "c_lvalk_of_expr: InitListExpr"
  | ImplicitValueInitExpr -> error "c_lvalk_of_expr: ImplicitValueInitExpr"
  | StmtExpr _ -> error "c_lvalk_of_expr: StmtExpr"
  | AddrLabelExpr _ -> error "c_lvalk_of_expr: AddrLabelExpr"
  | SizeOfExpr _ -> error "c_lvalk_of_expr: SizeOfExpr"
  | SizeOfType _ -> error "c_lvalk_of_expr: SizeOfType"
  | AlignOfExpr _ -> error "c_lvalk_of_expr: AlignOfExpr"
  | AlignOfType _ -> error "c_lvalk_of_expr: AlignOfType"
  | VecStepExpr _ -> error "c_lvalk_of_expr: VecStepExpr"
  | VecStepType _ -> error "c_lvalk_of_expr: VecStepType"
  | expr -> error ("c_lvalk_of_expr: " ^ (Pp.string_of_expr_ expr))

and c_lval_of_expr
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (expr: Clang.Ast.expr)
  : C_sig.c_lval =
  { clk = c_lvalk_of_expr clang c_types env decl_env expr ;
    clt = DenseIntMap.find expr.e_type.t_self c_types     }

and c_exprk_of_expr
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (expr: expr): C_sig.c_exprk =
  let line = start_line clang expr.e_sloc in
  let unimp s =
    Log.fatal_exn "%s at line %d\n%s\n"
      s line (Lib.get_line !Flags.analyzed_file line)
  in
  let error s =
    Log.fatal_exn "%s at line %d" s line
  in
  match expr.e with
  | IntegerLiteral i -> Ceconst (Ccint i)
  | StringLiteral s -> Ceconst (Ccstring s)
  | CharacterLiteral c -> Ceconst (Ccchar c)
  | BinaryOperator (op, lhs, rhs) ->
    Cebin (c_binop_of_binary_operator op clang expr.e_sloc,
           c_expr_of_expr clang c_types env decl_env lhs,
           c_expr_of_expr clang c_types env decl_env rhs)
  | UnaryOperator (UO_AddrOf, expr) ->
    Ceaddrof (c_lval_of_expr clang c_types env decl_env expr)
  | UnaryOperator (op, expr) ->
    begin
      match op with
      | UO_Plus -> c_exprk_of_expr clang c_types env decl_env expr
      | _ -> Ceuni (c_uniop_of_unary_operator op,
                    c_expr_of_expr clang c_types env decl_env expr)
    end
  | ParenExpr expr -> c_exprk_of_expr clang c_types env decl_env expr
  | CStyleCastExpr _ -> unimp "c_exprk_of_expr: CStyleCastExpr"
  | ImplicitCastExpr _ -> unimp "c_exprk_of_expr: ImplicitCastExpr"
  | FloatingLiteral _ -> unimp "c_exprk_of_expr: FloatingLiteral"
  | PredefinedExpr _ -> unimp "c_exprk_of_expr: PredefinedExpr"
  | CompoundLiteralExpr _ -> unimp "c_exprk_of_expr: CompoundLiteralExpr"
  | VAArgExpr _ -> unimp "c_exprk_of_expr: VAArgExpr"
  | CallExpr (e, _) -> unimp ("c_exprk_of_expr: CallExpr" ^ (Pp.string_of_expr e))
  | ConditionalOperator _ -> unimp "c_exprk_of_expr: ConditionalOperator"
  | DesignatedInitExpr _ -> unimp "c_exprk_of_expr: DesignatedInitExpr"
  | InitListExpr _ -> unimp "c_exprk_of_expr: InitListExpr"
  | ImplicitValueInitExpr -> unimp "c_exprk_of_expr: ImplicitValueInitExpr"
  | StmtExpr _ -> unimp "c_exprk_of_expr: StmtExpr"
  | AddrLabelExpr _ -> unimp "c_exprk_of_expr: AddrLabelExpr"
  | SizeOfExpr _  -> unimp "c_exprk_of_expr: SizeOfExpr"
  | SizeOfType tloc -> let size = sizeof clang tloc.tl_type in
                       (* Log.info "size: %d" size; *) (* debug *)
                       Ceconst (Ccint size)
  | AlignOfExpr _ -> unimp "c_exprk_of_expr: AlignOfExpr"
  | AlignOfType _ -> unimp "c_exprk_of_expr: AlignOfType"
  | VecStepExpr _ -> unimp "c_exprk_of_expr: VecStepExpr"
  | VecStepType _ -> unimp "c_exprk_of_expr: VecStepType"
  (* Already handled below. *)
  | ArraySubscriptExpr _ -> error "c_exprk_of_expr: ArraySubscriptExpr"
  | MemberExpr _ -> error "c_exprk_of_expr: MemberExpr"
  | DeclRefExpr _ -> error "c_exprk_of_expr: DeclRefExpr"
  | expr -> unimp ("c_exprk_of_expr: " ^ (Pp.string_of_expr_ expr))

and c_expr_of_expr
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (expr: Clang.Ast.expr): C_sig.c_expr =
  let c_type = DenseIntMap.find expr.e_type.t_self c_types in
  match expr.e with
  (* (( void* )0) => null *)
  | CStyleCastExpr
      (_,
       { tl = PointerTypeLoc { tl = BuiltinTypeLoc BT_Void } },
       { e = IntegerLiteral 0 }) ->
    { cek = Ceconst Ccnull;
      cet = c_type }
  | UnaryOperator (UO_Deref, _)
  | ArraySubscriptExpr _
  | MemberExpr _
  | DeclRefExpr _ ->
    (*print_endline (Show.show<expr> expr);*)
    (*print_endline (Show.show<ctyp> ty);*)
    { cek = Celval (c_lval_of_expr clang c_types env decl_env expr);
      cet = c_type }
  | _ ->
    (* print_endline (Pp.string_of_expr expr); *)
    { cek = c_exprk_of_expr clang c_types env decl_env expr;
      cet = c_type }

let make_call
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (callee: Clang.Ast.expr)
    (args: Clang.Ast.expr list): C_sig.c_call =
  { cc_fun = c_expr_of_expr clang c_types env decl_env callee;
    cc_args = List.map (c_expr_of_expr clang c_types env decl_env) args }

let get_return_type = For_memcad.Transformation.SplitInitialisers.get_return_type

let rec c_stat_of_expr
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (expr: Clang.Ast.expr): C_sig.c_stat =
  let loc = start_line clang expr.e_sloc in
  let unimp s =
    Log.fatal_exn "%s at line %d\n%s\n"
             s loc (Lib.get_line !Flags.analyzed_file loc)
  in
  match expr.e with
  | BinaryOperator (BO_Assign, lhs, rhs) ->
    (*print_endline (Show.show<expr> rhs);*)
    { csl = loc;
      csk = Csassign (c_lval_of_expr clang c_types env decl_env lhs,
                      c_expr_of_expr clang c_types env decl_env rhs) }
  | CallExpr (callee, args) ->
    { csl = loc;
      csk = (* Special handling for known functions. Note that
               malloc is not handled here, since it is only used
               within an assignment expression statement. *)
        let fun_name = Query.identifier_of_expr callee.e in
        match fun_name, args with
        | "_memcad", [{ e = StringLiteral str }] ->
          Cs_memcad (Mc_comstring str)
        | "assert", [_] ->
          Csassert (c_expr_of_expr clang c_types env decl_env (List.hd args))
        | "exit", [_] -> Csexit
        | "free", [_] ->
          Csfree (c_lval_of_expr clang c_types env decl_env (List.hd args))
        | _ ->
          let ret_type = get_return_type expr in
          let call = make_call clang c_types env decl_env callee args in
          if ret_type.t = BuiltinType BT_Void then (* procedure call *)
            let _ = Log.info "procedure call: %s" fun_name in
            Cspcall call
          else (* function call *)
            Log.fatal_exn "function call without lval to store its result: %s"
              fun_name
    }
  | DeclRefExpr _ -> (* ignored; transformed to an empty block *)
    { csl = loc; csk = Csblock [] }
  | IntegerLiteral _ -> unimp "c_stat_of_expr: IntegerLiteral"
  | CharacterLiteral _ -> unimp "c_stat_of_expr: CharacterLiteral"
  | FloatingLiteral _ -> unimp "c_stat_of_expr: FloatingLiteral"
  | StringLiteral _ -> unimp "c_stat_of_expr: StringLiteral"
  | BinaryOperator _ -> unimp "c_stat_of_expr: BinaryOperator"
  | UnaryOperator _ -> unimp "c_stat_of_expr: UnaryOperator"
  | PredefinedExpr _ -> unimp "c_stat_of_expr: PredefinedExpr"
  | ImplicitCastExpr _ -> unimp "c_stat_of_expr: ImplicitCastExpr"
  | CStyleCastExpr _ -> unimp "c_stat_of_expr: CStyleCastExpr"
  | CompoundLiteralExpr _ -> unimp "c_stat_of_expr: CompoundLiteralExpr"
  | ParenExpr _ -> unimp "c_stat_of_expr: ParenExpr"
  | VAArgExpr _ -> unimp "c_stat_of_expr: VAArgExpr"
  | MemberExpr _ -> unimp "c_stat_of_expr: MemberExpr"
  | ConditionalOperator _ -> unimp "c_stat_of_expr: ConditionalOperator"
  | DesignatedInitExpr _ -> unimp "c_stat_of_expr: DesignatedInitExpr"
  | InitListExpr _ -> unimp "c_stat_of_expr: InitListExpr"
  | ImplicitValueInitExpr -> unimp "c_stat_of_expr: ImplicitValueInitExpr"
  | ArraySubscriptExpr _ -> unimp "c_stat_of_expr: ArraySubscriptExpr"
  | StmtExpr _ -> unimp "c_stat_of_expr: StmtExpr"
  | AddrLabelExpr _ -> unimp "c_stat_of_expr: AddrLabelExpr"
  | SizeOfExpr _ -> unimp "c_stat_of_expr: SizeOfExpr"
  | SizeOfType _ -> unimp "c_stat_of_expr: SizeOfType 3"
  | AlignOfExpr _ -> unimp "c_stat_of_expr: AlignOfExpr"
  | AlignOfType _ -> unimp "c_stat_of_expr: AlignOfType"
  | VecStepExpr _ -> unimp "c_stat_of_expr: VecStepExpr"
  | VecStepType _ -> unimp "c_stat_of_expr: VecStepType"
  | expr -> unimp ("c_stat_of_expr: " ^ (Pp.string_of_expr_ expr))

(* This function maps N clang statements to M memcad statements.
   M may be considerably more than N.
   The output env. may contain local forward function declarations.
   Local function fwd. decls. are only supported in the body of a function,
   not in a while stmt, if stmt, etc. *)
let rec c_stats_of_stmts
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decl_env: C_sig.c_var StringMap.t)
    (stmts: Clang.Ast.stmt list): env * C_sig.c_block =
  let rec loop env decl_env stats = function
    | [] -> (env, stats)
    | stmt :: tl ->
      let csl = start_line clang stmt.s_sloc in
      let unimp msg =
        Log.fatal_exn "%s at line %d" msg csl
      in
      match stmt.s with
      | ReturnStmt expr ->
        let stat =
          { csl;
            csk = Csreturn
                (match expr with
                 | None -> None
                 | Some expr ->
                   Some (c_expr_of_expr clang c_types env decl_env expr)) }
        in
        loop env decl_env (stat :: stats) tl
      | ExprStmt e ->
        let stat = match e with
          (* Special handling of malloc. *)
          | { e = BinaryOperator
                  (BO_Assign, lhs, { e = CallExpr (callee, [arg]) }) }
            when Query.identifier_of_expr callee.e = "malloc" ->
            { csl;
              csk = Csalloc (c_lval_of_expr clang c_types env decl_env lhs,
                             c_expr_of_expr clang c_types env decl_env arg) }
          (* Special handling of assigned call expressions. *)
          | { e = BinaryOperator
                  (BO_Assign, lhs, { e = CallExpr (callee, args) }) } ->
            let fun_name = Query.identifier_of_expr callee.e in
            let _ = Log.info "function call: %s" fun_name in
            { csl;
              csk = Csfcall (c_lval_of_expr clang c_types env decl_env lhs,
                             make_call clang c_types env decl_env callee args) }
          | e ->
            (* printf "e: %s\n%!" (Pp.string_of_expr e); *)
            c_stat_of_expr clang c_types env decl_env e
        in
        loop env decl_env (stat :: stats) tl
      (* We only accept single declarations. *)
      | DeclStmt [decl] -> begin
          match c_decl_of_decl clang c_types env decl with
          | Loc_cvar (loc, c_decl) ->
            let decl_env = StringMap.add c_decl.cv_name c_decl decl_env in
            let stat = { csl = loc; csk = Csdecl c_decl } in
            loop env decl_env (stat :: stats) tl
          | Env (_env, c_fun) ->
            (* local function forward declaration *)
            loop (add_fun c_fun env) decl_env stats tl
        end
      | WhileStmt (cond, body) ->
        let stmts = Query.body_of_stmt body in
        let while_cond = c_expr_of_expr clang c_types env decl_env cond in
        let while_body =
          snd (c_stats_of_stmts clang c_types env decl_env stmts)
        in
        let no_unrolling = None in (* hard-coded "no loop unrolling" *)
        let csk = Cswhile (while_cond, while_body, no_unrolling) in
        let stat = { csl; csk } in
        loop env decl_env (stat :: stats) tl
      | IfStmt (cond, then_body, else_body) ->
        let stat =
          let then_stmts = Query.body_of_stmt then_body in
          let else_stmts = match else_body with
            | None -> []
            | Some else_body -> Query.body_of_stmt else_body
          in
          { csl;
            csk = Csif (c_expr_of_expr clang c_types env decl_env cond,
                        snd (c_stats_of_stmts
                               clang c_types env decl_env then_stmts),
                        snd (c_stats_of_stmts
                               clang c_types env decl_env else_stmts)) }
        in
        loop env decl_env (stat :: stats) tl
      | BreakStmt ->
        let stat = { csl; csk = Csbreak } in
        loop env decl_env (stat :: stats) tl
      | CompoundStmt stmts ->
        let env, c_stats = c_stats_of_stmts clang c_types env decl_env stmts in
        let stat = { csl; csk = Csblock c_stats } in
        loop env decl_env (stat :: stats) tl
      | NullStmt -> (* null statements are converted to an empty block;
                       since it's equivalent but supported by memcad's AST *)
        let stat = { csl; csk = Csblock [] } in
        loop env decl_env (stat :: stats) tl
      | ContinueStmt ->
          let stat = { csl ; csk = Cscontinue } in
          loop env decl_env (stat :: stats) tl
      | LabelStmt _ -> unimp "LabelStmt"
      | CaseStmt _ ->
        (* don't implement: should be handled by switchToIf *)
        unimp "CaseStmt"
      | DefaultStmt _ ->
        (* don't implement: should be handled by switchToIf *)
        unimp "DefaultStmt"
      | SwitchStmt _ ->
        (* don't implement: should be handled by switchToIf *)
        unimp "SwitchStmt"
      | GotoStmt _ -> unimp "GotoStmt"
      | ForStmt _ ->
        (* don't implement: should be handled by forToWhile *)
        unimp "ForStmt"
      | DoStmt _ ->
        (* don't implement: should be handled by doToWhile *)
        unimp "DoStmt"
      | DeclStmt _ -> unimp "DeclStmt"
      | stmt -> unimp (Pp.string_of_stmt_ stmt)
  in
  (* We build the list in reverse. *)
  let env, stats = loop env decl_env [] stmts in
  (env, List.rev stats)

let make_decl_env (env: env)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (tloc_: Clang.Ast.tloc_): env * C_sig.c_var StringMap.t =
  let init = (env, StringMap.empty) in
  match tloc_ with
  | FunctionProtoTypeLoc (_, args) ->
    List.fold_left
      (fun (env, decl_env) decl ->
         let env, parm = c_var_of_parm_decl env c_types decl in
         (env, StringMap.add parm.cv_name parm decl_env))
      init
      args
  | FunctionNoProtoTypeLoc _ -> init
  | tl -> Log.fatal_exn "make_decl_env: %s" (Pp.string_of_tloc_ tl)

(* find structs without typedef used for the first time in some statements *)
let collect_structs_no_typedef_in_stmts
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (stmts: Clang.Ast.stmt list): env =
  List.fold_left
    (fun env s -> match s with
       | { s = DeclStmt decls } ->
         List.fold_left
           (fun env d -> match d with
              | { d = VarDecl (ty, _name, _init) } ->
                add_struct_type ty env c_types
              | _ -> env)
           env
           decls
       | _ -> env)
    env
    stmts

(* find structs without typedef used for the first time in some declarations *)
let rec collect_structs_no_typedef_in_decls
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decls: decl list): env =
  match decls with
  | [] -> env
  | { d = RecordDecl (_ttk, name1, Some members, _) }
    :: { d = FieldDecl {
        fd_type = ({
          tl = ElaboratedTypeLoc {
              tl = RecordTypeLoc (kind, name2);
              tl_type;
            }
        } as ty);
        fd_name = name;
        fd_bitw = bitwidth;
        fd_init = init;
      } } :: tl when name1 = name2 ->
    let env = add_struct_type ty env c_types in
    let env = collect_structs_no_typedef_in_decls c_types env members in
    collect_structs_no_typedef_in_decls c_types env tl
  | { d = RecordDecl (_ttk, _name, None (* members *), _) } :: tl ->
    (* this is a forward declaration introduced by clang, just ignore it
       as it is not a field *)
    collect_structs_no_typedef_in_decls c_types env tl
  | { d = FieldDecl { fd_type = ty;
                      fd_name = name;
                      fd_bitw = bitwidth;
                      fd_init = init;
                      fd_index } } :: tl ->
    let env = add_struct_type ty env c_types in
    collect_structs_no_typedef_in_decls c_types env tl
  | { d } :: tl ->
    print_endline (Pp.string_of_decl_ d);
    Log.fatal_exn "collect_structs_no_typedef_in_decls: \
                   Only FieldDecls allowed within RecordDecl"

let c_fun_body_of_stmts
    (name: string)
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (ty: Clang.Ast.tloc)
    (body: Clang.Ast.stmt): env * C_sig.c_block =
  let stmts = Query.body_of_stmt body in
  let env = collect_structs_no_typedef_in_stmts c_types env stmts in
  let delayed_inits = (* if this is the main function, we have to prepend inits
                         of global variables to its statements *)
    if name <> "main" then []
    else begin
      saw_main := true;
      collect_delayed_init_stmts env
    end
  in
  let env, decl_env = make_decl_env env c_types ty.tl in
  c_stats_of_stmts clang c_types env decl_env (delayed_inits @ stmts)

(* transform each constant of an enum into an integer variable declaration *)
let int_vars_of_enum clang enumerators =
  let tl_type = For_memcad.Transformation.Codegen.int_type clang in
  let expr_of_int i sloc =
    let e = IntegerLiteral i in
    let e_cref = Ref.null in
    let e_sloc = sloc in
    let e_type = tl_type in
    { e ; e_cref ; e_sloc ; e_type }
  in
  let tloc_of_builtin_type bt sloc =
    let tl = BuiltinTypeLoc bt in
    let tl_cref = Ref.null in
    let tl_sloc = sloc in
    { tl ; tl_cref ; tl_sloc ; tl_type }
  in
  let rec loop acc prev_expr = function
    | [] -> List.rev acc
    | ({ d = EnumConstantDecl (name, maybe_init) } as decl) :: decls ->
      let init = match maybe_init with
        | Some init_expr -> init_expr
        | None -> (* increment previous one *)
          let int_one = expr_of_int 1 decl.d_sloc in
          { prev_expr with e = BinaryOperator (BO_Add, prev_expr, int_one) }
      in
      let tloc = tloc_of_builtin_type BT_Int decl.d_sloc in
      loop
        ({ decl with d = VarDecl (tloc, name, Some init) } :: acc)
        init
        decls
    | d :: decls ->
      Log.fatal_exn "transform.ml: int_vars_of_enum: %s"
        (Pp.string_of_decl d)
  in
  match enumerators with
  | [] -> []
  | decl :: _ ->
    let init_expr = expr_of_int (-1) decl.d_sloc in
    loop [] init_expr enumerators

let rec collect_decls
    (clang: Clang.Api.clang)
    (c_types: (Clang.Ast.ctyp, C_sig.c_type) Util.DenseIntMap.t)
    (env: env)
    (decls: Clang.Ast.decl list): env =
  match decls with
  | [] -> env
  | { d = EmptyDecl } :: tl -> collect_decls clang c_types env tl
  | { d = FunctionDecl (ty, DN_Identifier name, maybe_body) } :: tl ->
    (* Create the head of the function (without body), first,
       so that name lookups within the (eventual) body work for the
       currently processed function name. *)
    let env, c_fun = create_c_fun_forward_decl clang c_types env ty name in
    (* Log.info "c_fun: %s" (C_utils.c_fun_2stri "" c_fun); *)
    begin match maybe_body with
      | None -> (* Forward function declaration (without def.) / signature *)
        collect_decls clang c_types (add_fun c_fun env) tl
      | Some stmts -> (* Function definition *)
        let (env, c_fun) =
          let env' =
            if StringMap.mem name env.prog.cp_funs
            then env (* don't add the header of the function again in the env.
                        we already saw it in a forward declaration *)
            else add_fun c_fun env
          in
          let env, body =
            c_fun_body_of_stmts name clang c_types env' ty stmts
          in
          (env, { c_fun with cf_body = body })
        in
        collect_decls clang c_types (add_fun c_fun env) tl
    end
  (* Clang turns this code:
       typedef struct foo { int a } bar;
     into this:
       struct foo { int a };
       typedef struct foo bar;
     but there is no way to express these things in the memcad AST,
     and the memcad parser doesn't parse it, so we match this construct
     explicitly and transform it to the appropriate memcad AST. *)
  | { d = RecordDecl (_, name1, Some members, _) }
    :: { d = TypedefDecl (
        { tl = ElaboratedTypeLoc { tl = RecordTypeLoc (_, name2);
                                   tl_type }
             (* Handle "typedef struct foo *Foo;" (where struct foo was not
                yet defined) specially, as well. *)
             | PointerTypeLoc { tl = ElaboratedTypeLoc {
                 tl = RecordTypeLoc (_, name2);
                 tl_type } }
             (* handles: "typedef struct { char c; } buf[2];" *)
             | ConstantArrayTypeLoc ({ tl = ElaboratedTypeLoc {
                 tl = RecordTypeLoc (_, name2);
                 tl_type }
               }, _) }, name) }
    :: tl when name1 = name2 ->
    let c_type = DenseIntMap.find tl_type.t_self c_types in
    let env = add_type name c_type env in
    let env = collect_structs_no_typedef_in_decls c_types env members in
    collect_decls clang c_types env tl
  (* There may be other typedefs involving a preceding record definition,
     so this case is printed with a better diagnostic than the catch-all
     case below. *)
  | { d = RecordDecl (_, name, members, _) as decl }
    :: { d = TypedefDecl _ as tdef }
    :: tl ->
    Log.fatal_exn "unsupported record/typedef combination: [%s;\n%s;]"
      (Pp.string_of_decl_ decl)
      (Pp.string_of_decl_ tdef)
  | { d = RecordDecl (_, name, maybe_members, _) } :: tl ->
    let env = match maybe_members with
      | None -> env
      | Some members -> collect_structs_no_typedef_in_decls c_types env members
    in
    (* a record decl without a typedef will allow to see a new type only
       later once it is used *)
    collect_decls clang c_types env tl
  | { d = TypedefDecl (ty, name) } :: tl ->
    let c_type = DenseIntMap.find ty.tl_type.t_self c_types in
    collect_decls clang c_types (add_type name c_type env) tl
  | { d = VarDecl (ty, name, maybe_init) } as decl :: tl ->
    (* var decl at file scope with optional initialization *)
    let env = add_struct_type ty env c_types in
    begin match maybe_init with
      | None -> begin match c_decl_of_decl clang c_types env decl with
          | Loc_cvar (loc, c_var) ->
            collect_decls clang c_types (add_var c_var env) tl
          | Env _ -> assert(false);
        end
      | Some init ->
        let env = add_delayed_init decl env in
        collect_decls clang c_types env
          ({ decl with d = VarDecl (ty, name, None) } :: tl)
    end
  | { d = EnumDecl (_name, enumerators) } :: tl ->
    let var_decls = int_vars_of_enum clang enumerators in
    collect_decls clang c_types env (var_decls @ tl)
  | { d = LinkageSpecDecl (decls, lang) } :: tl ->
    collect_decls clang c_types (collect_decls clang c_types env decls) tl
  | { d = NamespaceDecl (name, inline, decls) } :: tl ->
    let env = { env with ns = env.ns ^ name ^ "::" } in
    collect_decls clang c_types (collect_decls clang c_types env decls) tl
  | { d = EnumConstantDecl    _ } :: _ ->
    Log.fatal_exn "EnumConstantDecl found at file scope"
  | { d = FieldDecl           _ } :: _ ->
    Log.fatal_exn "FieldDecl found at file scope"
  | { d = ParmVarDecl         _ } :: _ ->
    Log.fatal_exn "ParmVarDecl found at file scope"
  | { d = TranslationUnitDecl _ } :: _ ->
    Log.fatal_exn "nested TranslationUnitDecl found"
  | { d } :: _ ->
    Log.fatal_exn "%s" (Pp.string_of_decl_ d)

let array_iteri2 f a1 a2 =
  let n = Array.length a1 in
  assert(n = Array.length a2);
  for i = 0 to n - 1 do
    f i a1.(i) a2.(i)
  done

let decls_from_decl (debug: bool) (clang: Clang.Api.clang) (decl: Clang.Ast.decl): env =
  match decl with
  | { d = TranslationUnitDecl decls } ->
    C_process.max_c_var_id := 0;
    let env = { prog = C_utils.empty_unit;
                ns = ""; (* FBR: I think this namespace is never used *)
                delayed_init_vars = StringSet.empty;
                delayed_init_decls = [] } in
    let types = Api.(request clang @@ CacheFor Cache_ctyp) in
    let c_types = map_types clang types in
    if debug then (* display the map of types *)
      begin
        let clang_types = Util.DenseIntMap.to_array types in
        let memcad_types = Util.DenseIntMap.to_array c_types in
        Log.info "### types";
        array_iteri2
          (fun i t1 t2 ->
             Log.info ("### type %d ####################\n" ^^
                       "clang: %s\n" ^^
                       "### ----------------------------\n" ^^
                       "memcad: %s")
               i (Pp.string_of_ctyp t1) (C_utils.c_type_2str t2))
          clang_types memcad_types;
      end;
    let res = collect_decls clang c_types env decls in
    if (!saw_global_init && (not !saw_main)) then
      Log.warn "c_prog_from_decl: ignored global variable initialization";
    res
  | _ -> Log.fatal_exn "c_prog_from_decl requires a translation unit"

let c_prog_from_decls (decls: env): C_sig.c_prog =
  C_process.bind_c_prog decls.prog
