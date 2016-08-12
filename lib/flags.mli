(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: flags.mli
 ** global flags
 ** Xavier Rival, 2011/05/30 *)
open Data_structures

(** This file contains the global flags, and local debugging flags.
 *
 * It is organized as follows:
 * - Temporary flags (to be removed after ongoing refactoring
 * - Input
 * - Parsing
 * - ABI assumptions
 * - Output format
 * - Core interpreter
 * - Abstract domain (shape), structure
 * - Abstract domain (shape), parameterization
 * - Abstract domain (shape), inductive pre-analysis
 * - Abstract domain (arrays)
 * - Abstract domain (values)
 * - Abstract domain (disjs)
 * - Timing
 * - Debugging and sanity checks
 **)

(** Temporary flags *)
(* SV upgrading, to remove when the SV upgrade is done *)
val sv_upg: bool

(** Input *)
(* file name root *)
val filebase: string ref
(* Name of the file being analyzed *)
val analyzed_file: string ref
(* Main function *)
val mainfun: string ref
(* The analyzed code may have recursive calls *)
val rec_calls: bool ref

(** Parsing *)
(* to not use clang *)
val use_old_parser: bool ref
(* the C header file used by clang *)
val clang_header_fn: string ref
(* dump file after clang and transformations *)
val dump_parse: bool ref
(* read in a previous parse_dump *)
val load_dump: bool ref
(* control log level during transformations *)
val transforms_log_level: string ref

(** ABI assumptions *)
val abi_ptr_size:  int
val abi_int_size:  int
val abi_bool_size: int
val abi_char_size: int

(** Output format *)
(* whether to print the null offset *)
val flag_pp_off0: bool
(* whether to print default size information *)
val flag_pp_size4: bool
(* whether to print node infos other than edges *)
val flag_pp_nodeinfos: bool ref
(* whether to print node attributes *)
val flag_pp_nodeattr: bool
(* whether to print node allocation status *)
val flag_pp_nodealloc: bool
(* latex output enable *)
val flag_latex_output: bool ref
(* display the timing result (turn off for easier compare) *)
val flag_pp_timing: bool ref
(* output format *)
type output_format = (* might be extended with Tikz for LaTeX *)
  (* produces a .dot file for all or only the listed variable names *)
  | Out_dot of string list * string list (* (variable names, display options) *)
(* export all points *)
val flag_enable_ext_export_all: bool ref
(* disable timing module to prevent shadowing of exceptions *)
val no_analyze_prog_timer: bool ref
(* show call graph from entry point *)
val show_reachable_functions: bool ref

(** Core interpreter, iteration strategy and widening parameters *)
(* Statement status *)
val flag_status_decl:     bool ref
val flag_status_block:    bool ref
(* Logging of assertion test results *)
val flag_log_assert: bool
(* Use of a liveness pre-analysis *)
val do_live_analysis: bool
(* Loop unrolls *)
val unrolls: int ref
(* Type unfolding *)
val type_unfolds: int ref
(* Whether to unroll inner loops *)
val unroll_inner: bool ref
(* Directed weakening iterations *)
val dweak_iters: int ref
(* Join iterations before widening *)
val join_iters: int ref
(* Activation threshold widening *)
val widen_do_thr: bool ref
(* Temporary feature: built in list of widening parameters *)
val widen_thresholds: IntSet.t ref
(* Canonicalization-like abstraction for shape graphs
 * during join and widen *)
val widen_can: bool ref
(* Whether to merge right disjuncts before a join or widening *)
val disj_merge_before_join: bool ref
(* Guided join (makes memcad join less smart if turned off) *)
val guided_join: bool ref

(** Shape domain (shape), structure *)
(* domain structure *)
val shapedom_struct: string ref
(* domain structure type *)
type shape_dom =
  | Shd_flat                           (* flat, summary-less abstract domain *)
  | Shd_all                            (* all inductive definitions *)
  | Shd_list                           (* abstract domain specific for lists *)
  | Shd_inds of string list            (* some inductive definitions *)
  | Shd_sep of shape_dom * shape_dom   (* separating product of abstraction *)
  | Shd_prod of shape_dom * shape_dom  (* product of abstractions *)

(** Abstract domain (shape), parameterization *)
(* whether to trigger a gc phase after each assign *)
val do_gc_on_assign: bool
(* whether to perform incremental bottom reduction in the numerical domain *)
val do_raise_on_bottom: bool
(* whether to perform unary abstraction on graphs (kind of canonicalization) *)
val do_unary_abstraction: bool ref
(* whether to accelerate ind-ind rule when left is provably empty,
 * as it corresponds to a null pointer, empty heap *)
val do_quick_ind_ind_mt: bool ref
(* whether back indexes should be used *)
val flag_back_index: bool
val flag_debug_back_index: bool ref
val flag_gc_incr: bool (* whether back indexes should be used for gc *)
val flag_gc_full: bool ref (* whether full gc should be ran *)
(* Whether we should keep gc statistics, and print at the end *)
val flag_gc_stat: bool
(* Whether to use fast (incomplete) rule selection in unfold for is_le *)
val flag_unfold_sel: bool
(* Whether to use attribute before trying to generate an inductive *)
val flag_weaken_use_attribute: bool
(* Allow the join algorithm to by-pass rules that fail *)
val flag_join_bypass_fail_rules: bool
(* Allow the join to consider parameters of inductives as prioritary *)
val flag_join_parameters_prio: bool
(* Maximal number of unfolds *)
val max_unfold: int
(* Maximal number of cell read *)
val max_cell_read: int
(* Maximal number of cell resolve *)
val max_cell_resolve: int

(** Abstract domain (shape), inductive pre-analysis *)
(* Whether to activate the inductive analysis *)
val flag_indpars_analysis: bool ref
(* Whether the ind. def was inferred automatically *)
val auto_ind: bool ref
(* Control of the inductive definitions analysis *)
type ind_analysis_verbosity = 
  (* print nothing *)
  | No_verbose           
  (* print only computed invariant found at the end *)
  | Print_only_result    
  (* print each iteration *)
  | Print_each_iter
  (* print every operations (join, meet etc) *)
  | Print_all
val flag_ind_analysis_verbose: ind_analysis_verbosity ref

(** Graph encoding behavior *)
(* Control ignoring of prev pointers in inductives upon graph encoding *)
val no_ind_prev_fields: bool ref

(** Abstract domain (combinations): reduction and path language *)
(* Type of reduction mode *)
type reduction_mode = 
  | Rm_disabled
  | Rm_manual
  | Rm_minimal
  | Rm_on_read
  | Rm_on_read_and_unfold
  | Rm_maximal
(* Pp *)
val red_mode_2str: reduction_mode -> string
(* mode selector *)
val reduction_mode_selector: reduction_mode ref
(* maximum number of internal reduction iterations *)
val pl_internal_reduction_iteration: int
(* perform a sanity check before any operation *)
val pl_do_sanity_check_before: bool
(* maximum number of iteration of the inductive pre-analysis *)
val pl_max_ind_analysis_iter: int

(** Abstract domain (arrays) *)
val enable_array_domain: bool ref
val ljc_debug:  string -> unit
(** Abstract domain (values) *)
(* Kind of numerical domain *)
type num_dom = ND_box | ND_oct | ND_pol
(* Pretty-print of numerical domain kind *)
val num_dom_2str: num_dom -> string
(* Numerical domain selector *)
val nd_selector: num_dom ref
(* Kind of set domain *)
type set_dom = SD_none | SD_bdd | SD_lin | SD_quicr
(* Pretty-print of numerical domain kind *)
val set_dom_2str: set_dom -> string
(* Set domain selector *)
val sd_selector: set_dom ref
(* Whether to use the submemory abstraction *)
val enable_submem: bool ref
val submem_inds: StringSet.t ref
(* Whether to use a dynamic environment of symbolic variables *)
val enable_dynenv: bool ref
(* Dump sequences of operations *)
val flag_dump_ops: bool ref

(** Abstract domain (disjs) *)
(* Enabling the disjunction domain *)
val disj_selector: bool ref
(* Enabling keeping partitions through loops *)
val part_through_lfps: bool ref
(* selection widening *)
val sel_widen: bool ref
(* old widen *)
val old_widen: bool ref

(** Analysis outputs *)
(* Configuration report *)
val pp_config_report: unit -> unit
(* Statistics *)
val enable_stats: bool ref
(* Whether we should keep reduction statistics, and print at the end *)
val flag_reduction_stat: bool
(* Communication of the results on a pipe for reg testing *)
(* whether or not to send the results on a pipe *)
val use_pipe: bool ref
(* name of the pipe to be used *)
val pipe_name: string

(** Debugging and sanity checks *)
(* Pp all results (or just test) *)
val test_verbose: bool ref
(* Sanity checks (for debuging the domains) *)
val flag_sanity_pshape: bool (* prod shape domain *)
val flag_sanity_sshape: bool (* sep shape domain *)
val flag_sanity_bshape: bool (* base shape domain *)
val flag_sanity_ldom:   bool (* base list  domain *)
val flag_sanity_fshape: bool (* flat shape domain *)
val flag_sanity_frag:   bool
val flag_sanity_graph:  bool ref
val flag_sanity_env:    bool ref
val flag_sanity_env_pp: bool
val flag_sanity_disj:   bool ref
(* System *)
val flag_debug_open_file:      bool
val flag_debug_keygen:         bool
val flag_debug_c_frontend:     bool
(* Front-ends and translations *)
val flag_debug_type_ops:       bool
(* reduction *)
val flag_debug_reduction:      bool ref
(* path language *) 
(* antoine: similar to flag_debug_back_index for pl *)
val flag_debug_pl_back_info:   bool
val flag_debug_pl_join:        bool
val flag_debug_pl_rules:       bool
val flag_debug_pl_sanity:      bool
(* Pre-analyses and strategies *)
val flag_debug_live_analysis:  bool ref
val flag_debug_ind_analysis:   bool ref
(* Domain, C level *)
val flag_debug_scopes:         bool ref
(* Analysis *)
val flag_debug_uids:           bool
val flag_debug_iter:           bool ref
val flag_debug_funcalls:       bool
(* Symbolic variables management *)
val flag_debug_symvars:        bool ref
(* Graph blocks management *)
val flag_debug_frag:           bool ref
val flag_debug_graph_blocks:   bool ref
val flag_debug_block_sat:      bool ref
val flag_debug_array_blocks:   bool ref
val flag_debug_submem:         bool ref
(* Domain operations *)
val flag_debug_shape_abs:      bool ref
val flag_debug_abs_env:        bool ref
val flag_debug_is_le_gen:      bool ref
val flag_debug_is_le_shape:    bool ref
val flag_debug_is_le_list:     bool ref
val flag_debug_is_le_num:      bool ref
val flag_debug_is_le_strategy: bool ref
val flag_debug_join_gen:       bool ref
val flag_debug_join_shape:     bool ref
val flag_debug_join_list:      bool ref
val flag_debug_join_num:       bool ref
val flag_debug_join_strategy:  bool ref
val flag_debug_dweak_shape:    bool ref
val flag_debug_dweak_num:      bool ref
val flag_debug_dweak_strategy: bool ref
val flag_debug_materialize:    bool ref
val flag_debug_unfold:         bool ref
val flag_debug_bwd_unfold:     bool ref
val flag_debug_trigger_unfold: bool ref
val flag_debug_weak_abs:       bool ref
val flag_debug_disj:           bool ref
(* Transfer functions *)
val flag_debug_dommem_eval:    bool ref (* tr/rd of expr/lval *)
val flag_debug_dommem_evalx:   bool ref (* idem + more info *)
val flag_debug_domfshape:      bool ref
val flag_debug_guard:          bool ref
val flag_debug_assign:         bool ref
val flag_debug_sat:            bool ref
(* Checking the presence of inductives *)
val flag_debug_check_ind:      bool ref
(* Graph strategies *)
val flag_debug_gr_strat:       bool ref
(* List domain *)
val flag_debug_list_dom:       bool ref
(* Numerical domain *)
val flag_debug_num_env:        bool ref
val flag_debug_num_apron:      bool ref
val flag_display_num_env:      bool ref
(* Silent testing *)
val debug_disable: unit -> unit

(** Timing *)
(* Very silent testing, for timing *)
val very_silent_mode: bool ref
val very_silent: unit -> unit
(* Timing modules *)
val timing_apron:        bool ref
val timing_bshape:       bool ref (* base shape domain *)
val timing_lshape:       bool ref (* ad hoc list domain *)
val timing_fshape:       bool ref (* flat shape domain *)
val timing_pshape:       bool ref (* product shape domain *)
val timing_sshape:       bool ref (* sep shape domain *)
val timing_mem_exprs:    bool ref (* dom_mem_exprs *)
val timing_env:          bool ref
val timing_value:        bool ref
val timing_valset:       bool ref
val timing_graph_encode: bool ref
val timing_disj:         bool ref

(** Statistics *)
(* Count numbers of structures created *)
val stat_apron:        bool ref
