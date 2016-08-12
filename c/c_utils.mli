(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_utils.mli
 **       utilities for the micro C frontend
 ** Xavier Rival, 2011/07/16 *)
open C_sig
open Ast_sig

(** Helpers for the parsing *)
(* Creation of variables *)
val make_c_var: string -> c_type -> c_var
(* Creation of type-less typed expressions and l-values *)
val mkve: c_exprk -> c_expr
val mkvl: c_lvalk -> c_lval
(* Transformation of one type into another *)
val unbox_clval_in_cexpr: c_expr -> c_lval
val unbox_cstat_block: c_stat -> c_block
val unbox_cstat_in_declaration: parsed_declaration -> c_stat
val unbox_c_var_in_declaration: parsed_declaration -> c_var
(* managing environments *)
val empty_unit: c_prog
val add_fundef: c_type * string * c_var list * c_stat list -> c_prog -> c_prog
val add_typedef: parsed_declaration -> c_prog -> c_prog

(** Pretty-printing of C abstract syntax trees *)
val c_type_2stri: ?decl: bool -> string -> c_type -> string
val c_type_2str:  ?decl: bool -> c_type -> string
val c_typedef_2stri: string -> string * c_type -> string
val c_const_2str: c_const -> string
val c_uniop_2str: c_uniop -> string
val c_binop_2str: c_binop -> string
val c_var_2str: c_var -> string
val c_exprk_2str: c_exprk -> string
val c_expr_2str:  c_expr -> string
val c_lvalk_2str: c_lvalk -> string
val c_lval_2str:  c_lval -> string
val c_decl_2stri: string -> c_var -> string
val c_memcad_setvar_2str: c_memcad_setvar -> string
val c_memcad_setvars_2str: c_memcad_setvar list -> string
val c_memcad_iparams_opt_2str: c_memcad_iparams option -> string
val c_memcad_setexprs_2str: c_memcad_setexpr list -> string
val c_memcad_2stri: c_memcad_com -> string
val c_stat_2stri: string -> c_stat -> string
val c_block_2stri: string -> c_block -> string
val c_fun_2stri: string -> c_fun -> string
val c_prog_2stri: string -> c_prog -> string

(** MemCAD string utilities *)
val parse_memcad_comstring: c_memcad_com -> c_memcad_com

(** Other pp support stuffs *)
val c_stat_do_pp_status: c_stat -> bool

(** Types and storage *)
(* Functions to elaborate representation of types, with size and align info *)
val c_type_elaborate: c_type -> c_type
(* Functions to read the align and types *)
val c_type_alignof: c_type -> int
val c_type_sizeof: c_type -> int

(** Extraction of program elements *)
val get_function: c_prog -> string -> c_fun

(** Utility functions on expressions *)
(* Negation of conditions *)
val c_expr_neg: c_expr -> c_expr
(* Extraction of a function name out of a call (ptr calls non supported) *)
val c_call_name: c_call -> string

(** Basic utilities for types *)
(* Compatibility test, used for, e.g.:
 *  - verification of assignments, modulo pointer type casts
 *  - verification of index data types
 * (i.e., all pointers are considered a void* ) *)
val c_type_compat: c_type -> c_type -> bool
(* Read name *)
val c_type_read_named: c_type -> c_type
(* Binary typing *)
val c_type_binary: c_binop -> c_type -> c_type -> c_type
(* Unary typing *)
val c_type_unary: c_uniop -> c_type -> c_type
(* Read a struct type and returns a field *)
val c_type_read_struct_field: c_type -> string -> c_type
(* Read a pointer type, and returns underlying *)
val c_type_read_ptr: c_type -> c_type
(* Read a type for array cell read out *)
val c_type_read_array: c_type -> c_type -> c_type

(** Iteration function over types in the program *)
val c_prog_apply_type_op: (c_type -> c_type) -> c_prog -> c_prog

(** Translations between C and abstract domain syntax *)
val tr_c_type: c_type -> typ
val tr_c_var: c_var -> var
val tr_c_const: c_const -> const
val tr_c_field: c_type -> string -> field
val tr_c_exprk: c_exprk -> var expr
val tr_c_expr: c_expr -> var texpr
val tr_c_lvalk: c_lvalk -> var lval
val tr_c_lval: c_lval -> var tlval
val tr_c_setvar: c_memcad_setvar -> setvar
val tr_c_setexpr: c_memcad_setexpr -> var tlval setprop
