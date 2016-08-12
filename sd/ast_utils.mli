(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ast_utils.mli
 **       utilities on abstract syntax trees
 ** Xavier Rival, 2011/05/27 *)
open Apron
open Ast_sig
open Nd_sig

(** Some basic iterators on expressions, lvalues and set properties *)
val map_expr: ('a -> 'b) -> 'a expr -> 'b expr
val map_texpr: ('a -> 'b) -> 'a texpr -> 'b texpr
val map_lval: ('a -> 'b) -> 'a lval -> 'b lval
val map_tlval: ('a -> 'b) -> 'a tlval -> 'b tlval
val map_setprop: ('a -> 'b) -> (setvar -> int) -> 'a tlval setprop 
  -> 'b tlval setprop

(** Named types *)
val tnamed_find: string -> typ
val tnamed_add: string -> typ -> unit

(** Utilities on types *)
val sizeof_typ: typ -> int
val alignof_typ: typ -> int
val find_field: typ_struct -> string -> typ_sfield
val field_2off: field -> Offs.t
val typ_is_ptr: typ -> bool

(** Pretty-printing of expressions, and lvalues *)
val typ_2str: typ -> string
val uni_op_2str: uni_op -> string
val bin_op_2str: bin_op -> string
val const_2str: const -> string
val field_2str: field -> string
val expr_2str: ('a -> string) -> 'a expr -> string
val texpr_2str: ('a -> string) -> 'a texpr -> string
val lval_2str: ('a -> string) -> 'a lval -> string
val tlval_2str: ('a -> string) -> 'a tlval -> string
val condtree_2str: ('a -> string) -> 'a condtree -> string

(** Printers for c-vars *)
val var_2str:    var -> string
val vexpr_2str:  var  expr -> string
val vtexpr_2str: var texpr -> string
val vlval_2str:  var  lval -> string
val vtlval_2str: var tlval -> string
val vcondtree_2str: var condtree -> string

(** Printers for int *)
val iexpr_2str:  int  expr -> string
val itexpr_2str: int texpr -> string
val ilval_2str:  int  lval -> string
val itlval_2str: int tlval -> string
val icondtree_2str: int condtree -> string

(** Typing *)
(* Computing well typed expressions and conditions *)
val type_texpr: (var -> typ) -> var texpr -> var texpr
val type_expr:  (var -> typ) -> var expr  -> var texpr
val type_tlval: (var -> typ) -> var tlval -> var tlval
val type_lval:  (var -> typ) -> var lval  -> var tlval

(** Binding *)
val bind_var:   (string -> int) -> var -> var
val bind_texpr: (string -> int) -> var texpr -> var texpr
val bind_tlval: (string -> int) -> var tlval -> var tlval

(** Extraction of condition trees *)
(* Simply pulls condition operators at the top into another ast.
 * This will make treatment of the guard operator easier *)
val extract_tree: 'a texpr -> 'a condtree

(** Translation of operators *)
(*val tr_uni_op: uni_op -> Texpr1.unop*)
val tr_bin_op: bin_op -> Texpr1.binop

(** Translation of conditions *)
(* Utilities *)
val texpr_is_rand_cell: 'a texpr -> bool
val texpr_is_const: 'a texpr -> bool
val make_apron_op: bin_op -> Lincons0.typ
(* Generic function
 * (actually, cannot be used as is in dom_shape_flat *)
val gen_tr_tcond: ('a -> int texpr -> 'a * n_expr)
  -> 'a -> int texpr -> 'a * n_cons
