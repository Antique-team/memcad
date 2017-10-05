(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_sig.ml
 **       signatures of the main abstract domains
 ** Xavier Rival, started 2011/05/27 *)
open Data_structures
open Flags
open Lib
open Offs

open Ast_sig
open Disj_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Set_sig
open Sv_sig
open Svenv_sig


(** Location (for the disjunctions domain to keep track of partitions) *)
type location = int (* we should keep this more generic *)

(** Carrying out names through printers *)

(* For the numerical domain *)
type sv_namer = string IntMap.t (* maps certain SVs to a string *)


(** Join kind *)
type join_kind =
  | Jjoin  (* real join, may not terminate *)
  | Jwiden (* widening, enforces termination *)
  | Jdweak (* directed weakening, over approximates only right side *)


(** Symbolic variables mappings communicated to the domain *)
(* Unary operations that require a set of roots *)
type 'a uni_table = 'a Aa_sets.t
(* Relations between left argument (L), right argument (R) and output (O) *)
type 'a bin_table = ('a, 'a) Aa_maps.t        (* R => L function *)
type 'a tri_table = ('a * 'a * 'a) Aa_sets.t  (* set of (L, R, O) mappings *)


(** Hints to be supplied to graph algorithms *)
(* We use structures here, in anticipation of additional hints added in the
 * near future *)

(* Shape domain level, for local weak abstraction (Unary) *)
type 'a hint_us =
    { hus_live: 'a uni_table }
(* Shape domain level, for widening and join (Binary) *)
type 'a hint_bs =
    { hbs_live: 'a bin_table }
type 'a lint_bs = (* TODO: the "lint_" names is wierd, and should be changed *)
    { lbs_dead: 'a bin_table }

(* Environment level, for local weak abstraction (Unary) *)
type hint_ue =
    { hue_live: VarSet.t (* live variables *) }
(* Environment level, for widening and join (Binary) *)
type hint_be =
    { hbe_live: VarSet.t; (* live variables in both argument *) }
type 'a lint_be =
    { lbe_dead:  ('a tlval) list; (*dead access path*)}

(* Joining element with encoded graph *)
type join_ele =
  { (* the encoding of input graph *)
    abs_gi:   abs_graph option;
    (* the join result of encodings *)
    abs_go:   abs_graph option; }


(** Symbolic variables mapping, returned by lattice operations *)
(* Symbolic variable updater *)
type sv_upd =
  | Svu_mod of int * IntSet.t (* sv is modified *)
  | Svu_rem                   (* sv is removed *)
(* Symbolic variable environment updater *)
type svenv_upd = int -> sv_upd

(** Inductive calls *)
type 'a gen_ind_intp =
  | Ii_const of int
  | Ii_lval of 'a
type 'a gen_ind_pars =
    { ic_ptr:  'a list ;
      ic_int:  'a gen_ind_intp list ; (* integer parameters *)
      ic_set:  setvar list;           (* set parameters*) }
type 'a gen_ind_call =
    { ic_name: string; (* inductive that is called *)
      ic_pars: 'a gen_ind_pars option (* parameters, if supplied *) }


(** Localization of an SV in a sub-memory *)
(* Computed localization *)
type sub_localize =
  | Sl_unk     (* cannot be proved to be in the block *)
  | Sl_inblock of int (* proved to be in the block, but not found *)
  | Sl_found of int * Offs.t (* SV is at some known offset *)
(* Destination inside a sub-memory *)
type sub_dest =
  | Sd_env of int * Offs.t (* (s,o): submem SV s and offset o from s *)
  | Sd_int of int * Offs.t (* (i,o): global SV i and offset o from i *)


(** Right-value, used for write functions in the dom_value layer *)
(* - either an expression *)
type n_rval =
  | Rv_expr of n_expr
  | Rv_addr of int * Offs.t (* to-update *)


(** Type for symbolic variables:
 ** -> this type is actually probably going to be replaced with a
 **    more general description of SV types (module sv_sig) *)
type sv = int
type svo = sv * Offs.t
(* Types for the transition *)
type svt =
  | Sv_old of sv
  | Sv_new of Sv_sig.sv_id
type svot = svt * Offs.t


(** Types for commands that are shared across domains *)
(* Inductive predicates (call-src, node-srce) *)
type 'a indt = 'a gen_ind_call * 'a
(* Segment predicates (call-src, node-src, call-dst, node-dst) *)
type 'a segt = 'a gen_ind_call * 'a * 'a gen_ind_call * 'a

(* Logical formulas, used for specifying assumed/checked properties *)
(* State-level abstractions (mem-low, mem-high, state) *)
type 'a gen_st_log_form =
  | SL_array
  | SL_set of 'a setprop  (* set predicate *)
  | SL_ind of 'a indt     (* inductive predicate *)
  | SL_seg of 'a segt     (* segment predicate *)
type meml_log_form  = svo gen_st_log_form       (* vars: sv+off *)
type memh_log_form  = int tlval gen_st_log_form (* vars: sv-lvalues *)
type state_log_form = var tlval gen_st_log_form (* vars: lang-lvalues *)

(* Environment commands *)
type env_op =
  | EO_add_var of var       (* Add C-level Var *)
  | EO_del_var of var       (* Del C-level Var *)
  | EO_add_setvar of setvar (* Add C-level Set-Var *)
  | EO_del_setvar of setvar (* Del C-level Set-Var *)

(* Memory commands *)
type 'a mem_op =
  | MO_alloc of 'a tlval * 'a texpr (* Allocation:       l = malloc( e ) *)
  | MO_dealloc of 'a tlval          (* Deallocation:     free( l )       *)
type int_mem_op = int mem_op
type var_mem_op = var mem_op

(* Unary op in the disj domain *)
type unary_op =
  | UO_env of env_op     (* addition/deletion of (set) variables *)
  | UO_ret of typ option (* addition of return var or not *)
  | UO_mem of var_mem_op (* memory operations *)

(* Assume commands for the value domain: just array for now *)
type vassume_op =
  | VA_array
  | VA_aseg of int * Offs.t * svo gen_ind_call
        * int * Offs.t * svo gen_ind_call
  | VA_aind of int * Offs.t * svo gen_ind_call

(* Check commands for the value domain *)
type vcheck_op =
  | VC_array
  | VC_ind of int * Offs.t * string (* l = ind( ) *)
  | VC_aseg of int * Offs.t * svo gen_ind_call
        * int * Offs.t * svo gen_ind_call
  | VC_aind of int * Offs.t * svo gen_ind_call


(** Domain to represent values:
 **  An abstract value represents a set of functions from integer
 **  labeled symbolic variables into values (numeric integer or
 **  floating point values, boolean values, sub-memories)
 **  [all of which are not handled yet]
 **  [set symbolic variables should also appear here in the future]
 **)
module type DOM_VALUE =
  sig
    include INTROSPECT
    (** Type of abstract values *)
    type t
    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    val init_inductives: Keygen.t -> StringSet.t -> Keygen.t
    (** Lattice elements *)
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Top element *)
    val top: t
    (* Pretty-printing, takes a namer for SVs *)
    val t_2stri: sv_namer -> string -> t -> string
    (** Management of symbolic variables *)
    (* For sanity check *)
    val check_nodes: IntSet.t -> t -> bool
    (* SV addition and removal *)
    val add_node: int -> t -> t
    val rem_node: int -> t -> t
    (* Renaming (e.g., post join) *)
    val symvars_srename:
        (Offs.t * int) OffMap.t -> (int * Offs.t) node_mapping -> t -> t
    (* Synchronization of the SV environment *)
    val sve_sync_top_down: svenv_mod -> t -> t
    (* Check the symbolic vars correspond exactly to given set *)
    val symvars_check: IntSet.t -> t -> bool
    (* Removes all symbolic vars that are not in a given set *)
    val symvars_filter: IntSet.t -> t -> t
    (* Merging into a new variable, arguments:
     *  . the stride of the structure being treated
     *  . SV serving as a base address of a block;
     *  . SV serving as a new block abstraction (as a sequence of bits)
     *  . old contents of the block, that is getting merged
     *  . offsets of external pointers into the block to build an environment *)
    val symvars_merge: int -> int -> int -> (Bounds.t * onode * Offs.size) list
      -> OffSet.t -> t -> t
    (** Comparison and join operators *)
    (* Comparison *)
    val is_le: t -> t -> (int -> int -> bool) -> bool
    (* Upper bound: serves as join and widening *)
    val upper_bnd: join_kind -> t -> t -> t
    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    val sat: t -> n_cons -> bool
    (** Condition test *)
    val guard: bool -> n_cons -> t -> t
    (** Assignment *)
    val assign: int -> n_expr -> t -> t
    (* Assignment inside a sub-memory *)
    val write_sub: sub_dest -> int -> n_rval -> t -> t
    (** Utilities for the abstract domain *)
    val simplify_n_expr: t -> n_expr -> n_expr
    (** Array domain specific functions *)
    (* Add an array content SV  *)
    val add_array_node: int -> int -> int list -> t -> t
    (* Add an array address SV  *)
    val add_array_address: int -> t -> t
    (* Checks wheter this SV is the address of an array SV *)
    val is_array_address: int -> t -> bool
    (* Dereference an array cell in experision,
     * this function may cause disjunction *)
    val array_node_deref: int -> Offs.t -> t -> (t * int) list
    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    val array_materialize: int -> Offs.t -> t -> t * int
    (* Summarzing dimensions related opeartions
     * expand the constraints on one dimension to another  *)
    val expand: int -> int -> t -> t
    (* Upper bound of the constraits of two dimensions *)
    val compact: int -> int -> t -> t
    (* Conjunction *)
    val meet: t -> t -> t
    (* Forget the information on a dimension *)
    val sv_forget: int -> t -> t
    (** Export of range information *)
    val bound_variable:int -> t -> interval
    (** Sub-memory specific functions *)
    (* Checks whether an SV is of sub-memory type *)
    val is_submem_address: int -> t -> bool
    val is_submem_content: int -> t -> bool
    (* Read of a value inside a submemory block *)
    val submem_read: (n_cons -> bool) -> int -> Offs.t -> int -> t -> onode
    val submem_deref: (n_cons -> bool) -> int -> Offs.t -> int -> t -> onode
    (* Localization of an SV in a sub-memory *)
    val submem_localize: int -> t -> sub_localize
    (* Binding of an offset in a sub-memory *)
    val submem_bind: int -> int -> Offs.t -> t -> t * onode
    (* Regression testing support, inside sub-memories *)
    val check:  vcheck_op  -> t -> bool
    val assume: vassume_op -> t -> t
    (* Unfolding *)
    val unfold: int -> nid -> unfold_dir -> t -> (int IntMap.t * t) list
    (* Get all variables that equal to a given SV *)
    val get_eq_class: int -> t -> IntSet.t
  end


(** Signature of maya domain.
 ** In this domain, each variable accounts for a may-empty set of values *)
module type DOM_MAYA =
  sig
    include INTROSPECT
    type t
    (** Pretty-printing *)
    val t_2stri: sv_namer -> string -> t -> string
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Assert that some variable is not empty *)
    val assert_non_empty: int -> t -> t
    (** Management of symbolic variables *)
    val rem_node: int -> t -> t
    val add_node: int -> bool -> int -> int option -> t -> t
    (* Forget the informaiton of a varialbe except its existence *)
    val sv_forget: int -> t -> t
    (* Merge the informaiton of two variables to one *)
    val compact: int -> int -> t -> t
    (* Narrow the type of all set variables from numeric information *)
    val narrow_set_vars: t -> t
    (* Comparision: variable-wise subset *)
    val is_incl: t -> t -> bool
    (* The bound of a variable *)
    val bound_variable: int -> t -> interval
    (* Reset the size of a scalar variable *)
    val scalar_to_single: int -> t -> t
    val scalar_to_exist: int -> t -> t
    (* Reset the size of a variable by an expression *)
    val size_assign: int -> n_expr -> t -> t
    (* Constrain the size of variables *)
    val size_guard: n_cons -> t -> t
    (* Comparison *)
    val is_le: t -> t -> bool
    (* Upper bound: serves as join and widening *)
    val upper_bnd: join_kind -> t -> t -> t
    (* Guard, strong version  *)
    val guard_s: bool -> n_cons -> t -> t
    (* Guard, weak version  *)
    val guard_w: bool -> n_cons -> t -> t
    (** Checks a constraint is satisfied (strong version vs weak version) *)
    val sat_w: t -> n_cons -> bool
    val sat_s: t -> n_cons -> bool
    (* Update, substitute the set with the value the expression *)
    val update_subs_set: int -> n_expr -> t -> t
    (* Update, substitute one element in the set with the value of the
     * expression *)
    val update_subs_elt: int -> n_expr -> t -> t
    (* Weak update, add one elt to a set  *)
    val update_add: int -> n_expr -> t -> t
    (* Strong update, remove one elt to a set  *)
    val update_rem: int -> n_expr -> t -> t
    (* Copy the information from a variable to another *)
    val expand: int -> int -> t -> t
    (* Rename a variable *)
    val rename_var: int -> int -> t -> t
    (* Filter variables *)
    val symvars_filter: IntSet.t -> t -> t
    (* Top element *)
    val top: t
    (* Get all variables that equal to a given SV *)
    val get_eq_class: int -> t -> IntSet.t
    (* Get namer *)
    val get_namer: sv_namer -> t -> unit
  end

(** Signature of the set+value domain:
 **  An abstract value represents a pair of valuations from:
 **  - symbolic variables to values
 **  - set variables to values
 **  The signature incorporates all the DOM_VALUE signature,
 **  and adds set properties as well.
 **  The elements that are specific to the set domain are marked "specific" *)
module type DOM_VALSET =
  sig
    include INTROSPECT
    (** Type of abstract values *)
    type t
    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    val init_inductives: Keygen.t -> StringSet.t -> Keygen.t
    (** Lattice elements *)
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Top element *)
    val top: t
    (* Pretty-printing, with indentation *)
    val t_2stri: sv_namer -> string -> t -> string
    (** Management of symbolic variables *)
    (* For sanity check *)
    val check_nodes: IntSet.t -> t -> bool
    (** Symbolic variables **)
    (* add symbolic variables, mark used to choose num or set *)
    val sv_add: ?mark:bool -> int -> t -> t
    val sv_rem: int -> t -> t
    (** Set variables **)
    (* add set var with the given name *)
    val setv_add: ?root: bool -> ?kind: set_par_type option
      -> ?name: string option -> int -> t -> t
    val setv_rem: int -> t -> t
    (* check if a set var is root or not *)
    val setv_is_root: int -> t -> bool
    (* collect root set variables*)
    val setv_col_root: t -> IntSet.t
    (* Renaming (e.g., post join), mark used to choose only rename set domain *
     * or rename both, specifically to join *)
    val symvars_srename: (* may change a little bit *)
      ?mark: bool -> (Offs.t * int) OffMap.t -> (int * Offs.t) node_mapping
        -> setv_mapping option -> t -> t
    (* Synchronization of the SV environment *)
    val sve_sync_top_down: svenv_mod -> t -> t (* may change a little bit *)
    (* Check the symbolic vars correspond exactly to given set *)
    val symvars_check: IntSet.t -> t -> bool (* may change a little bit *)
    (* Removes all symbolic vars that are not in a given set *)
    (* may change a little bit *)
    val symvars_filter: IntSet.t -> ?set_vars: IntSet.t ->  t -> t
    (* Merging into a new variable, arguments:
     *  . the stride of the structure being treated
     *  . SV serving as a base address of a block;
     *  . SV serving as a new block abstraction (as a sequence of bits)
     *  . old contents of the block, that is getting merged
     *  . offsets of external pointers into the block to build an environment *)
    val symvars_merge: int -> int -> int -> (Bounds.t * onode * Offs.size) list
      -> OffSet.t -> t -> t (* may change a little bit *)
    (** Comparison and join operators *)
    (* Comparison *)
    val is_le: t -> t -> (int -> int->bool) -> bool
    (* Upper bound: serves as join and widening *)
    val upper_bnd: join_kind -> t -> t -> t
    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    val sat: t -> n_cons -> bool
    (** Set satisfiability *)
    val set_sat: set_cons -> t -> bool (* specific *)
    (** Condition test *)
    val guard: bool -> n_cons -> t -> t
    (** Set condition test *)
    val set_guard: set_cons -> t -> t (* specific *)
    (** Assignment *)
    val assign: int -> n_expr -> t -> t
    (* Assignment inside a sub-memory *)
    val write_sub: sub_dest -> int -> n_rval -> t -> t
    (** Utilities for the abstract domain *)
    val simplify_n_expr: t -> n_expr -> n_expr
    (** Array domain specific functions *)
    (* Add an array content SV *)
    val sv_array_add: int -> int ->  int list -> t -> t
    (* Add an array address SV *)
    val sv_array_address_add: int -> t -> t
    (* Dhecks wheter this SV is the address of an array SV *)
    val is_array_address: int -> t -> bool
    (* Dereference an array cell in experision,
     * this function may cause disjunction *)
    val sv_array_deref: int -> Offs.t -> t -> (t * int) list
    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    val sv_array_materialize: int -> Offs.t -> t -> t * int
    (** Sub-memory specific functions *)
    (* Checks whether an SV is of sub-memory type *)
    val is_submem_address: int -> t -> bool
    val is_submem_content: int -> t -> bool
    (* Read of a value inside a submemory block *)
    val submem_read: (n_cons -> bool) -> int -> Offs.t -> int -> t -> onode
    val submem_deref: (n_cons -> bool) -> int -> Offs.t -> int -> t -> onode
    (* Localization of an SV in a sub-memory *)
    val submem_localize: int -> t -> sub_localize
    (* Binding of an offset in a sub-memory *)
    val submem_bind: int -> int -> Offs.t -> t -> t * onode
    (* Regression testing support, inside sub-memories *)
    val check:  vcheck_op  -> t -> bool
    val assume: vassume_op -> t -> t
    (* Unfolding *)
    val unfold: int -> nid -> unfold_dir -> t -> (int IntMap.t * t) list
    (** Summarzing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    val expand: int -> int -> t -> t
    (* Upper bound of the constraits of two dimensions *)
    val compact: int -> int -> t -> t
    (* Conjunction *)
    val meet: t -> t -> t
    (* Forget the information about an SV *)
    val sv_forget: int -> t -> t
    (** Export of range information *)
    val sv_bound: int -> t -> interval
    (* Get all variables that equal to a given SV *)
    val get_eq_class: int -> t -> IntSet.t
  end


(** Signature of the lower layer of the memory abstract domain
 **   - this layer deals with memory cells (creation, read, write)
 **   - memory domain combination operations are done at this level
 **)
module type DOM_MEM_LOW =
  sig
    include INTROSPECT
    (** Type of abstract values *)
    type t
    (** Domain initialization to a set of inductive definitions *)
    (* Domain initialization to a set of inductive definitions *)
    val init_inductives: Keygen.t -> StringSet.t -> Keygen.t
    val inductive_is_allowed: string -> bool
    (** Fixing sets of keys *)
    val sve_sync_bot_up: t -> t * svenv_mod
    (* Sanity check *)
    val sanity_sv: IntSet.t -> t -> bool
    (** Lattice elements *)
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Top element, with empty set of roots *)
    val top: unit -> t (* this is empty store, in fact *)
    (* Pretty-printing *)
    val t_2stri: string -> t -> string
    val t_2str: t -> string
    (* External output *)
    val ext_output: output_format -> string -> namer -> t -> unit
    (** Management of symbolic variables *)
    (* Will that symb. var. creation be allowed by the domain? *)
    val sv_is_allowed: ?attr:node_attribute -> ntyp -> nalloc -> t -> bool
    (* Add a symbolic variable, with a newly generated id
     *  (by default, not considered root by the underlying domain) *)
    val sv_add_fresh: ?attr:node_attribute -> ?root: bool -> ntyp -> nalloc
      -> t -> sv * t
    (* Recover information about a symbolic variable *)
    (* For now, only nalloc and ntyp *)
    val sv_get_info: sv -> t -> nalloc option * ntyp option
    (* Garbage collection *)
    val gc: sv uni_table -> t -> t
    (* graph encode *)
    val encode: int -> namer -> t -> renamed_path list * PairSetSet.t * int
    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    val is_le: sv bin_table -> sv bin_table -> t -> t
      -> svenv_upd option (* None = false *)
    (* Generic comparison (does both join and widening) *)
    val join: join_kind -> int hint_bs option -> (onode lint_bs) option
      -> int tri_table -> int tri_table -> t * join_ele -> t * join_ele
        -> t * svenv_upd * svenv_upd
    (* Directed weakening; over-approximates only the right element *)
    val directed_weakening: int hint_bs option
      -> int tri_table -> int tri_table -> t -> t -> t * svenv_upd
    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    val local_abstract: sv hint_us option -> t -> t
    (** Cell operations *)
    (* Creation *)
    val cell_create: ?attr:node_attribute -> svo -> Offs.size -> ntyp -> t -> t
    (* Deletion *)
    val cell_delete: ?free:bool -> ?root:bool -> sv -> t -> t
    (* Read the content of a cell *)
    val cell_read:
      bool                 (* whether call from cell-resolve  *)
      -> svo                (* address of the cell to read *)
      -> int               (* size of the cell to read *)
        -> t               (* abstract memory input *)
          -> (t            (* possibly modified memory abstraction *)
              * svo        (* address of the read cell, may have changed *)
              * svo option (* Some content in case of success, None otherwise *)
             ) list        (* list of disjuncts *)
    (* Resolve a cell, i.e., materialization *)
    val cell_resolve:
        svo          (* address of the cell to resolve *)
      -> int         (* size *)
        -> t         (* abstract memory input *)
          -> (t      (* possibly modified memory abstraction *)
              * svo  (* address of the resolved cell, may have changed *)
              * bool (* whether cell resolution was succesful *)
             ) list  (* list of disjuncts *)
    (* Write a cell *)
    val cell_write:
        ntyp          (* type of the value being assigned *)
      -> svo          (* address of the cell to over-write *)
        -> int        (* size of the chunk to write into the memory *)
          -> n_expr   (* right hand side as an expression over SVs *)
            -> t -> t (* output abstract memory *)
    (** Transfer functions for the analysis *)
    (* Condition test *)
    val guard: n_cons -> t -> t
    (* Checking that a constraint is satisfied *)
    val sat: n_cons -> t -> bool
    (** Set domain *)
    (* Adding / removing set variables *)
    val setv_add_fresh: bool -> string -> t -> int * t
    val setv_delete: int -> t -> t
    (* Guard and sat functions for set properties *)
    val assume: meml_log_form -> t -> t
    val check:  meml_log_form -> t -> bool
    (** Unfolding, assuming and checking inductive edges *)
    (* Unfold *)
    val ind_unfold: unfold_dir -> svo -> t -> t list
  end


(** Signature of the upper layer of the memory abstract domain
 **   - this layer solves the evaluation of expressions
 **   - it delegates the cell operations to DOM_MEM_LOW
 **   - a lift functor defines this from DOM_MEM_LOW
 **)
module type DOM_MEM_EXPRS =
  sig
    include INTROSPECT
    (** Type of abstract values *)
    type t
    (** Domain initialization to a set of inductive definitions *)
    (* Domain initialization to a set of inductive definitions *)
    val init_inductives: Keygen.t -> StringSet.t -> Keygen.t
    val inductive_is_allowed: string -> bool
    (** Fixing sets of keys *)
    val sve_sync_bot_up: t -> t * svenv_mod
    (* Sanity check *)
    val sanity_sv: IntSet.t -> t -> bool
    (** Lattice elements *)
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Top element, with empty set of roots *)
    val top: unit -> t (* this is empty store, in fact *)
    (* Pretty-printing *)
    val t_2stri: string -> t -> string
    val t_2str: t -> string
    (* External output *)
    val ext_output: output_format -> string -> namer -> t -> unit
    (* Garbage collection *)
    val gc: int uni_table -> t -> t
    (* graph encode *)
    val encode: int -> namer -> t -> renamed_path list * PairSetSet.t * int
    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    val is_le: int bin_table -> int bin_table -> t -> t -> bool
    (* Generic comparison (does both join and widening) *)
    val join: join_kind -> int hint_bs option -> ((int tlval) lint_bs) option
      -> int tri_table -> int tri_table -> t * join_ele -> t * join_ele -> t
    (* Directed weakening; over-approximates only the right element *)
    val directed_weakening: int hint_bs option -> int tri_table
      -> int tri_table -> t -> t -> t
    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    val local_abstract: int hint_us option -> t -> t
    (** Transfer functions for the analysis *)
    (* Assignment *)
    val assign: int tlval -> int texpr -> t -> t list
    (* Condition test *)
    val guard: bool -> int texpr -> t -> t list
    (* Checking that a constraint is satisfied *)
    val sat: int texpr -> t -> bool
    (* Creation of the memory for a variable *)
    val create_mem_var: typ -> t -> int * t
    (* Removal of the memory for a variable *)
    val delete_mem_var: int -> t -> t (* takes SV representing address *)
    (* memory alloc/free *)
    val memory: int_mem_op -> t -> t list
    (** Set domain *)
    (* generate / delete set variables *)
    val gen_setvar: string -> t -> int * t
    val del_setvar: int -> t -> t
    (* Guard and sat functions for set properties *)
    val assume: memh_log_form -> t -> t
    val check:  memh_log_form -> t -> bool
    (** Unfolding, assuming and checking inductive edges *)
    (* Unfold *)
    val ind_unfold: unfold_dir -> int tlval -> t -> t list
  end


(** Signature of the env+shape domain *)
module type DOM_ENV =
  sig
    include INTROSPECT
    (** Type of abstract values *)
    type t
    (* Bottom element *)
    val bot: t -> t (* transforms a value into a bottom *)
    val is_bot: t -> bool
    (* Top element, with provided set of roots *)
    val top: unit -> t
    (* Pretty-printing *)
    val t_2stri: string -> t -> string
    val t_2str: t -> string
    (* External output *)
    val ext_output: output_format -> string -> t -> unit
    (* Garbage collection *)
    val gc: t -> t
    (** Management of variables *)
    val unary_op: env_op -> t -> t
    (* encode graph *)
    val encode: int -> var list -> t -> renamed_path list *  PairSetSet.t * int
    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    val is_le: t -> t -> bool
    (* Generic comparison *)
    val gen_join: join_kind -> hint_be option -> (var lint_be) option
      -> t * join_ele -> t * join_ele -> t
    (* Join and widening *)
    val join:  hint_be option -> (var lint_be) option
      -> t * join_ele -> t * join_ele -> t
    val widen: hint_be option -> (var lint_be) option
      -> t * join_ele -> t * join_ele -> t
    val directed_weakening: hint_be option -> t -> t -> t
    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    val local_abstract: hint_ue option -> t -> t
    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    val assign: var tlval -> var texpr -> t -> t list
    (* Condition test *)
    val guard: bool -> var texpr -> t -> t list
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    val sat: var texpr -> t -> bool
    (* Memory alloc/free *)
    val memory: var_mem_op -> t -> t list
    (** Set domain *)
    (* Guard and sat functions for set properties *)
    val assume: state_log_form -> t -> t
    val check:  state_log_form -> t -> bool
    (** Analysis control *)
    (* Reduction + SV relocalization *)
    val reduce_localize: var tlval -> t -> t option
    (* Eager reduction *)
    val reduce_eager: t -> t list
    (** Assuming and checking inductive edges *)
    (* Unfold *)
    val ind_unfold: unfold_dir -> var tlval -> t -> t list
    (* Check construction, that an inductive be there *)
    (** Temporary, to short-cut disjunctions *)
    val assert_one: t list -> t
  end

(** Signature of the disjunction domain *)
module type DOM_DISJ =
  sig
    include INTROSPECT
    (* Abstract elements, with or without disjunctions *)
    type t
    (* Disjunction size *)
    val disj_size: t -> int
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Top element, with provided set of roots *)
    val top: unit -> t
    (* Pretty-printing *)
    val t_2stri: string -> t -> string
    val t_2str: t -> string
    (* External output *)
    val ext_output: output_format -> string -> t -> unit
    (* Garbage collection *)
    val gc: t -> t
    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    val is_le: t -> t -> bool
    (* Generic comparison *)
    val merge_disjuncts: t -> t (* joins symbolic disjunctions *)
    val join:  hint_be option -> (var lint_be) option -> t -> t -> t
    val widen: hint_be option -> (var lint_be) option -> t -> t
      -> t * (t option)
    val directed_weakening: hint_be option -> t -> t -> t
    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    val assign: location -> var tlval -> var texpr -> t -> t list
    (* Condition test *)
    val guard: location -> bool -> var texpr -> t -> t list
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    val sat: var texpr -> t -> bool
    (** Set domain *)
    (* Adding / removing set variables *)
    val unary_op: unary_op -> t -> t
    (* Guard and sat functions for set properties *)
    val assume: state_log_form -> t -> t
    val check:  state_log_form -> t -> bool
    (** Management of disjunctions *)
    (* Selective disjunct merge *)
    val sel_merge: var list -> hint_be option -> (var lint_be) option -> t -> t
    (* Adding an abs_hist_atom *)
    val push_hist_atom: abs_hist_atom -> t -> t
    (** Analysis control *)
    (* Reduction + SV relocalization *)
    val reduce_localize: var tlval -> t -> t
    (* Eager reduction *)
    val reduce_eager: t -> t
    (** Assuming and checking inductive edges *)
    (* Unfold *)
    val ind_unfold: location -> unfold_dir -> var tlval -> t -> t
    (** Statistics *)
    (* For now, simply a number of disjuncts *)
    val get_stats: t -> int
  end

module type GRAPH_ENCODE =
  sig
    include INTROSPECT
    type encoded_graph_edges = renamed_path list
    type encoded_graph = encoded_graph_edges * PairSetSet.t * int
    val can_widen: encoded_graph -> encoded_graph -> bool
    val encode: int -> namer -> graph -> encoded_graph
    val join: encoded_graph -> encoded_graph -> encoded_graph option
    val widen: encoded_graph -> encoded_graph -> encoded_graph
    val pp_encoded_graph:
      int -> string list -> graph -> namer -> string -> out_channel -> unit
    val pp_precisely_encoded_graph:
      int -> string list -> graph -> namer -> string -> out_channel -> unit
    val reduce_to_seg: abs_graph -> abs_graph
    val string_of_renamed_paths: encoded_graph_edges -> string
    val to_string: abs_graph_arg option -> string
    (* the following are for unit tests *)
    exception Cannot_join
    val is_included_any: step list -> step list -> bool
    val join_paths: renamed_path -> renamed_path -> renamed_path option
  end
