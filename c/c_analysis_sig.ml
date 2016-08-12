(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_analysis_sig.ml
 **       C level abstraction layers
 ** Xavier Rival, 2012/02/02 *)
open Ast_sig
open C_sig
open Data_structures
open Dom_sig
open Flags

type 'a unary_operand =
  | Add_var    of var * 'a
  | Remove_var of var * 'a

(** Generic liveness pre-analysis functor types
 **  - DOM_LIVENESS describes the abstract domains for the pre-analysis functor
 **  - PRE_ANALYSIS describes the type of the resulting analysis *)
module type DOM_LIVENESS =
  sig
    (* liveness information *)
    type var_paths
    (* empty *)
    val empty: var_paths
    val t_2str: var_paths -> string
    (* add/remove a variable to/from liveness *)
    val unary_op: var_paths unary_operand -> var_paths
    (* merge liveness information *)
    val read_merge: var_paths -> var_paths -> var_paths
    (* deal with write information from out *)
    val merge_out_write: var_paths -> var_paths -> var_paths
    (* deal with read information from out *)
    val merge_out_read: var_paths -> var_paths -> var_paths
    (* derefence an expression *)
    val deref_expr: var_paths -> c_lval -> var_paths
    (* access a field of an expression *)
    val field_expr: var_paths -> string -> c_lval -> var_paths
    (* access the address of an expression *)
    val addr_expr: var_paths -> var_paths
    (* check liveness inclusion, for computing fixpoint of while *)
    val is_inclusion: var_paths -> var_paths -> bool
    val t_paths: var_paths -> PathSet.t VarMap.t
  end

module type PRE_ANALYSIS =
  sig
    type live_status
    type live
    val live_prog: string -> c_prog -> live
    val live_at: int -> PathSet.t VarMap.t
  end

(** TODO XR => JL: add comments to these definitions *)
module type DOM_PRE_PROPERTY =
  sig
    type t
    val empty: t
    val t_2str: t -> string
    val equal: t -> t -> bool
    val assign: c_lval -> c_expr -> t -> t
    val guard: c_expr -> t -> t -> t
    val decl: c_var -> t -> t
    val alloc: c_lval ->c_expr  -> t -> t
    val free: c_lval  -> t -> t
    val assertion: c_expr -> t -> t
    val pcall: c_call -> c_fun -> t -> t
    val fcall: c_lval -> c_call -> c_fun -> t -> t
    val return: c_expr option -> t -> t
    val memcad: c_memcad_com -> t-> t
  end
module type PRE_PATH_SENSITIVE_ANALYSIS =
  sig
    type t
    type elt
    val pre_prog: string -> c_prog -> t
    val pro_at: int -> t-> elt
    val t_2str: t -> string
  end


(* For now, the C layer should account for various C level features:
 *  - variables scopes;
 *  - return variables
 *  - return branches
 *  - possibly branchings at a later point (e.g., break) *)

(** Unary operations on C flows *)
type 'a flow_op =
  | FO_block_in        (* entry into a block *)
  | FO_block_out       (* exit out of a block *)
  | FO_fun_in          (* entry into a function body *)
  | FO_fun_out of 'a   (* exit out of a function body *)
  | FO_loop_in         (* entry into a loop *)
  | FO_loop_out        (* exit out of a loop *)
  | FO_loop_body_in    (* entry into a loop body *)
  | FO_loop_body_out   (* exit out of a loop body *)
  | FO_branch_break    (* follow a break branch *)
  | FO_branch_continue (* follow a continue branch *)
  | FO_branch_return   (* follow a return branch *)
(* Pretty-printing of operations on flows *)
let flow_op_2str: 'a flow_op -> string = function
  | FO_block_in        -> "FO_block_in"
  | FO_block_out       -> "FO_block_out"
  | FO_fun_in          -> "FO_fun_in"
  | FO_fun_out _       -> "FO_fun_out"
  | FO_loop_in         -> "FO_loop_in"
  | FO_loop_out        -> "FO_loop_out"
  | FO_loop_body_in    -> "FO_loop_body_in"
  | FO_loop_body_out   -> "FO_loop_body_out"
  | FO_branch_break    -> "FO_branch_break"
  | FO_branch_continue -> "FO_branch_continue"
  | FO_branch_return   -> "FO_branch_return"

module type DOM_C =
  sig
    type t
    (* Bottom element *)
    val bot: t -> t
    val is_bot: t -> bool
    (* Top element, with provided set of roots *)
    val top: c_prog -> t
    (* Pretty-printing *)
    val t_2stri: string -> t -> string
    (* External output *)
    val ext_output: output_format -> string -> t -> t
    (* Management of variables, set variables, set expressions, etc. *)
    val unary_op: t -> Opd3.unary_operand -> t
    (* Management of inductive, segments, arrays, etc. *)
    val assume: t -> state_log_form -> t
    val check:  t -> state_log_form -> bool
    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    val is_le: t -> t -> bool
    (* Generic comparison *)
    val join:  hint_be option -> (var lint_be) option -> t -> t -> t
    val widen: hint_be option -> (var lint_be) option -> t -> t -> t * t option
    val directed_weakening: hint_be option -> t -> t -> t
    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    val assign: location -> var tlval -> var texpr -> t -> t list
    (* Condition test *)
    val guard: location -> bool -> var texpr -> t -> t list
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    val sat: var texpr -> t -> bool
    (** Assuming and checking inductive edges *)
    (* Unfold *)
    val ind_unfold: location -> Graph_sig.unfold_dir -> var tlval -> t -> t
    (** Regression testing *)
    (* Check invariant bottomness *)
    val check_bottomness: bool -> t -> bool
    (** Management of disjunctions *)
    val merge: t -> t
    val sel_merge: var list -> hint_be option -> (var lint_be) option -> t -> t
    val assert_one: string -> t list -> t
    (* Adding an abs_hist_atom *)
    val push_hist_atom: Disj_sig.abs_hist_atom -> t -> t
    (** Analysis control *)
    (* Reduction + node relocalization *)
    val reduce_localize: var tlval -> t -> t
    (* Eager reduction *)
    val reduce_eager: t -> t
    (** C specific operations *)
    (* Function calls *)
    val get_function: string -> t -> c_fun
    val restore_return_var: t -> t -> t
    (* Assign to/from the return variable *)
    val assign_to_return: location -> var texpr -> t -> t list
    val assign_from_return: location -> var tlval -> t -> t list
    (** Unary flow operations *)
    val unary_flow_op: t flow_op -> t -> t
    (* Managing loop count *)
    val loop_count: t -> int
    (** Statistics *)
    val get_stats: t -> Statistics.ainv_stats
  end
