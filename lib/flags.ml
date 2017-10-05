(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: flags.ml
 **       global flags
 ** Xavier Rival, 2011/05/25 *)
open Data_structures

module Log =
  Logger.Make(struct let section = "flags___" and level = Log_level.DEBUG end)

(** Temporary flags *)
(* SV upgrading, to remove when the SV upgrade is done *)
let sv_upg: bool = false

(** Input *)
(* file name root *)
let filebase: string ref = ref ""
(* Name of the file being analyzed *)
let analyzed_file: string ref = ref ""
(* Main function *)
let mainfun: string ref = ref "main"
(* The analyzed code may have recursive calls *)
let rec_calls: bool ref = ref false

(** Parsing *)
(* to not use clang *)
let use_old_parser: bool ref = ref false
(* the C header file used by clang *)
let clang_header_fn: string ref = ref "memcad.h"
(* additional directories where to look for C headers *)
let include_dirs: string ref = ref ""
(* dump file after clang and transformations *)
let dump_parse: bool ref = ref false
(* read in a previous parse dump *)
let load_dump: bool ref = ref false
(* control log level during transformations *)
let transforms_log_level: string ref = ref "info"

(** ABI assumptions *)
let abi_ptr_size:  int = 4
let abi_int_size:  int = 4 (* default, size of integers, assuming 32 bits *)
let abi_bool_size: int = 4 (* default, assuming C use of int *)
let abi_char_size: int = 1

(** Semantics *)
(* whether cases where malloc returns true are considered
 *  (false by default, as per the C semantics) *)
let flag_malloc_never_null: bool ref = ref false

(** Output format *)
(* whether to print the null offset *)
let flag_pp_off0: bool = false
(* whether to print default size information *)
let flag_pp_size4: bool = false
(* whether to print node infos other than edges *)
let flag_pp_nodeinfos: bool ref = ref true
(* whether to print node attributes *)
let flag_pp_nodeattr: bool = true
(* whether to print node allocation status *)
let flag_pp_nodealloc: bool = true
(* latex output enable *)
let flag_latex_output: bool ref = ref false
(* display the timing result (turn off for easier compare) *)
let flag_pp_timing: bool ref = ref true
(* output format *)
type output_format = (* might be extended with Tikz for LaTeX *)
  | Out_dot of string list * string list
(* export all points *)
let flag_enable_ext_export_all: bool ref = ref false
(* show call graph from entry point *)
let show_reachable_functions: bool ref = ref false

(** Core interpreter, iteration strategy and widening parameters *)
(* Statement status *)
let flag_status_decl:     bool ref = ref true
let flag_status_block:    bool ref = ref true
(* Logging of assertion test results *)
let flag_log_assert: bool = true
(* Use of a liveness pre-analysis *)
let do_live_analysis: bool = true
(* Loop unrolls *)
let unrolls: int ref = ref 0
(* Type unfolding *)
let type_unfolds: int ref = ref 1
(* Whether to unroll inner loops *)
let unroll_inner: bool ref = ref true
(* Directed weakening iterations *)
let dweak_iters: int ref = ref 0
(* Join iterations before widening *)
let join_iters: int ref = ref 0
(* Activation threshold widening *)
let widen_do_thr: bool ref = ref true
(* Temporary feature: built in list of widening parameters *)
let widen_thresholds: IntSet.t ref =
  ref (List.fold_left (fun a i -> IntSet.add i a) IntSet.empty [ 0; 10 ])
(* Canonicalization-like abstraction for shape graphs
 * during join and widen *)
let widen_can: bool ref = ref false
(* Whether to merge right disjuncts before a join or widening *)
let disj_merge_before_join: bool ref = ref false
(* Guided join (makes memcad join less smart if turned off) *)
let guided_join: bool ref = ref true
(* Guided widen (currently prototype feature in development) *)
let guided_widen: bool ref = ref true

(** Shape domain (shape), structure *)
(* domain structure *)
let shapedom_struct: string ref = ref "\"[@ll]\""
(* domain structure type *)
type shape_dom =
  | Shd_flat                           (* flat, summary-less abstract domain *)
  | Shd_all                            (* all inductive definitions *)
  | Shd_list                           (* abstract domain specific for lists *)
  | Shd_tvl                            (* TVL based shape domain *)
  | Shd_inds of string list            (* some inductive definitions *)
  | Shd_sep of shape_dom * shape_dom   (* separating product of abstraction *)
  | Shd_prod of shape_dom * shape_dom  (* product of abstractions *)

(** Abstract domain (shape), parameterization *)
(* whether to trigger a gc phase after each assign *)
let do_gc_on_assign: bool = true
(* whether to perform incremental bottom reduction in the numerical domain *)
let do_raise_on_bottom: bool = true
(* whether to perform unary abstraction on graphs (kind of canonicalization) *)
let do_unary_abstraction: bool ref = ref true
(* whether to accelerate ind-ind rule when left is provably empty,
 * as it corresponds to a null pointer, empty heap *)
let do_quick_ind_ind_mt: bool ref = ref true
(* whether back indexes should be used *)
let flag_back_index: bool = true
let flag_debug_back_index: bool ref = ref false
let flag_gc_incr: bool = true (* whether back indexes should be used for gc *)
let flag_gc_full: bool ref = ref true (* whether full gc should be ran *)
(* Whether we should keep gc statistics, and print at the end *)
let flag_gc_stat: bool = true
(* Whether to use fast (incomplete) rule selection in unfold for is_le *)
let flag_unfold_sel: bool = true
(* Whether to use attribute before trying to generate an inductive *)
let flag_weaken_use_attribute: bool = true
(* Allow the join algorithm to by-pass rules that fail *)
let flag_join_bypass_fail_rules: bool = true
(* Allow the join to consider parameters of inductives as prioritary *)
let flag_join_parameters_prio: bool = true
(* Maximal number of unfolds *)
let max_unfold: int = 3
(* Maximal number of cell read *)
let max_cell_read: int = 5
(* Maximal number of cell resolve *)
let max_cell_resolve: int = 5

(** Abstract domain (shape), inductive pre-analysis *)
(* Whether to activate the inductive analysis for parameters kinds *)
let flag_indpars_analysis: bool ref = ref true
(* Whether the ind. def was inferred automatically *)
let auto_ind: bool ref = ref false

(** Graph encoding behavior *)
(* Control ignoring of prev pointers in inductives upon graph encoding *)
let no_ind_prev_fields: bool ref = ref true

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
let flag_ind_analysis_verbose: ind_analysis_verbosity ref = ref No_verbose    

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
let red_mode_2str: reduction_mode -> string = function
  | Rm_disabled           -> "disabled"
  | Rm_manual             -> "manual"
  | Rm_minimal            -> "min"
  | Rm_on_read            -> "on-read"
  | Rm_on_read_and_unfold -> "on-r-u"
  | Rm_maximal            -> "max"
(* mode selector *)
let reduction_mode_selector: reduction_mode ref = ref Rm_disabled
(* maximum number of internal reduction iterations *)
let pl_internal_reduction_iteration: int = 5
(* perform a sanity check before any operation *)
let pl_do_sanity_check_before: bool = false
(* maximum number of iteration of the inductive pre-analysis *)
let pl_max_ind_analysis_iter: int = 5

(** Abstract domain (arrays) *)
let enable_array_domain: bool ref =  ref false

(** Equation Pack *)
let enable_eq_pack: bool ref =  ref false

(** Abstract domain (values) *)
(* Kind of numerical domain *)
type num_dom = ND_box | ND_oct | ND_pol
(* Pretty-print of numerical domain kind *)
let num_dom_2str: num_dom -> string = function
  | ND_box -> "box"
  | ND_oct -> "oct"
  | ND_pol -> "pol"
(* domain selector *)
let nd_selector: num_dom ref = ref ND_pol
(* Kind of set domain *)
type set_dom =
  | SD_none            (* no set domain *)
  | SD_lin             (* lin set domain, local implementation *)
  | SD_quicr           (* QUICr domain *)
  | SD_setr of string  (* SETr library *)
(* Pretty-print of numerical domain kind *)
let set_dom_2str: set_dom -> string = function
  | SD_lin    -> "lin"
  | SD_none   -> "none"
  | SD_quicr  -> "QUICr"
  | SD_setr n -> Printf.sprintf "SETr[%s]" n
(* Set domain selector *)
let sd_selector: set_dom ref = ref SD_none
(* Whether to use the submemory abstraction *)
let enable_submem: bool ref = ref false
let submem_inds: StringSet.t ref = ref StringSet.empty
(* Whether to use a dynamic environment of symbolic variables *)
let enable_dynenv: bool ref = ref true
(* Dump sequences of operations *)
let flag_dump_ops: bool ref = ref false

(** Abstract domain (disjs) *)
(* Enabling the disjunction domain *)
let disj_selector: bool ref = ref true
(* Enabling keeping partitions through loops *)
let part_through_lfps: bool ref = ref false
(* selection widening *)
let sel_widen: bool ref = ref false
(* old widen: a widen {b, c} = (a widen b) join (a widen c)*)
let old_widen: bool ref = ref false

(** Analysis outputs *)
(* Configuration report *)
let pp_config_report (): unit =
  let dom_disj = if !disj_selector then "ON" else "OFF" in
  let rm = match !reduction_mode_selector with
    | Rm_disabled           -> "OFF"
    | Rm_manual             -> "ON (Manual)"
    | Rm_minimal            -> "ON (Minimal)"
    | Rm_on_read            -> "ON (On read)"
    | Rm_on_read_and_unfold -> "ON (On read and unfold)"
    | Rm_maximal            -> "ON (Maximal)" in
  Log.info "==================================\nCONFIGURATION:";
  Log.info "Numerical domain:     %s" (num_dom_2str !nd_selector);
  Log.info "Set domain:           %s" (set_dom_2str !sd_selector);
  Log.info "Disjunction domain:   %s" dom_disj;      
  Log.info "Reduction mode:       %s" rm;
  Log.info "=================================="
(* Statistics *)
let enable_stats: bool ref = ref false
(* Whether we should keep reduction statistics, and print at the end *)
let flag_reduction_stat: bool = true
(* Communication of the results on a pipe *)
(* whether or not to send the results on a pipe *)
let use_pipe: bool ref = ref false
(* name of the pipe to be used *)
let pipe_name = "regtestpipe"

(** Debugging and sanity checks *)
(* Pp all results (or just test) *)
let test_verbose: bool ref = ref false
(* Sanity checks (for debuging the domains) *)
let flag_sanity_pshape: bool     = true  (* prod shape domain *)
let flag_sanity_sshape: bool     = true  (* sep shape domain *)
let flag_sanity_bshape: bool     = false (* base shape domain *)
let flag_sanity_ldom:   bool     = false (* base list  domain *)
let flag_sanity_fshape: bool     = false (* flat shape domain *)
let flag_sanity_frag:   bool     = false
let flag_sanity_graph:  bool ref = ref true
let flag_sanity_env:    bool ref = ref true
let flag_sanity_env_pp: bool     = false
let flag_sanity_disj:   bool ref = ref true
(* System *)
let flag_debug_open_file:      bool = true
let flag_debug_keygen:         bool = false
let flag_debug_c_frontend:     bool = true
(* Front-ends and translations *)
let flag_debug_type_ops:       bool = false
(* reduction *)
let flag_debug_reduction:      bool ref = ref true
(* path language *) 
(* antoine: similar to flag_debug_back_index for pl *)
let flag_debug_pl_back_info:   bool = false
let flag_debug_pl_join:        bool = false
let flag_debug_pl_rules:       bool = false
let flag_debug_pl_sanity:      bool = false
(* Pre-analyses and strategies *)
let flag_debug_live_analysis:  bool ref = ref true
let flag_debug_ind_analysis:   bool ref = ref true
(* Analysis *)
let flag_debug_uids:           bool = true
let flag_debug_iter:           bool ref = ref true
let flag_debug_funcalls:       bool = true
(* Symbolic variables management *)
let flag_debug_symvars:        bool ref = ref true
(* Domain, C level *)
let flag_debug_scopes:         bool ref = ref true
(* Graph blocks management *)
let flag_debug_frag:           bool ref = ref true
let flag_debug_graph_blocks:   bool ref = ref true
let flag_debug_block_sat:      bool ref = ref false
let flag_debug_array_blocks:   bool ref = ref true
let flag_debug_submem:         bool ref = ref true
(* Domain operations *)
let flag_debug_shape_abs:      bool ref = ref true
let flag_debug_abs_env:        bool ref = ref true
let flag_debug_is_le_gen:      bool ref = ref true
let flag_debug_is_le_shape:    bool ref = ref true
let flag_debug_is_le_list:     bool ref = ref true
let flag_debug_is_le_num:      bool ref = ref true
let flag_debug_is_le_strategy: bool ref = ref true
let flag_debug_join_gen:       bool ref = ref true
let flag_debug_join_shape:     bool ref = ref true
let flag_debug_join_list:      bool ref = ref true
let flag_debug_join_num:       bool ref = ref true
let flag_debug_dweak_shape:    bool ref = ref true
let flag_debug_dweak_num:      bool ref = ref true
let flag_debug_dweak_strategy: bool ref = ref true
let flag_debug_join_strategy:  bool ref = ref true
let flag_debug_materialize:    bool ref = ref false
let flag_debug_unfold:         bool ref = ref true
let flag_debug_bwd_unfold:     bool ref = ref true
let flag_debug_trigger_unfold: bool ref = ref true
let flag_debug_weak_abs:       bool ref = ref true
let flag_debug_disj:           bool ref = ref true
(* Transfer functions *)
let flag_debug_dommem_eval:    bool ref = ref true (* tr/rd of expr/lval *)
let flag_debug_dommem_evalx:   bool ref = ref false (* idem + more info *)
let flag_debug_domfshape:      bool ref = ref true
let flag_debug_guard:          bool ref = ref true
let flag_debug_assign:         bool ref = ref true
let flag_debug_sat:            bool ref = ref false
(* Checking the presence of inductives *)
let flag_debug_check_ind:      bool ref = ref false
(* Graph strategies *)
let flag_debug_gr_strat:       bool ref = ref false
(* List domain *)
let flag_debug_list_dom:       bool ref = ref true
(* Numerical domain *)
let flag_debug_num_env:        bool ref = ref false
let flag_debug_num_apron:      bool ref = ref true
let flag_display_num_env:      bool ref = ref true
(* Silent testing *)
let debug_disable ( ) =
  let l_flags =
    [ (* reduction *)
      flag_debug_reduction      ; flag_debug_live_analysis  ;
      flag_debug_ind_analysis   ; 
      (* Symbolic variables management *)
      flag_debug_symvars        ;
      (* Domain, C level *)
      flag_debug_scopes         ;
      (* Graph blocks management *)
      flag_debug_frag           ; flag_debug_graph_blocks   ;
      flag_debug_block_sat      ; flag_debug_array_blocks   ;
      flag_debug_submem         ;
      (* Domain operations *)
      flag_debug_shape_abs      ; flag_debug_abs_env        ;
      flag_debug_is_le_gen      ; flag_debug_is_le_shape    ;
      flag_debug_is_le_list     ; flag_debug_is_le_num      ;
      flag_debug_is_le_strategy ; flag_debug_join_gen       ;
      flag_debug_join_shape     ; flag_debug_join_list      ;
      flag_debug_join_num       ; flag_debug_join_strategy  ;
      flag_debug_dweak_shape    ; flag_debug_dweak_num      ;
      flag_debug_dweak_strategy ; flag_debug_materialize    ;
      flag_debug_unfold         ; flag_debug_bwd_unfold     ;
      flag_debug_trigger_unfold ; flag_debug_weak_abs       ;
      flag_debug_dommem_eval    ; flag_debug_dommem_evalx   ;
      flag_debug_domfshape      ; flag_debug_disj           ;
      flag_debug_guard          ; flag_debug_assign         ;
      flag_debug_gr_strat       ; flag_debug_list_dom       ;
      flag_debug_num_env        ; flag_debug_num_apron      ;
      flag_display_num_env      ; flag_debug_check_ind      ] in
  List.iter (fun r -> r := false) l_flags

(** Timing *)
(* Very silent testing, for timing *)
let very_silent_mode: bool ref = ref false
let very_silent (): unit =
  flag_debug_iter   := false;
  very_silent_mode  := true;
  debug_disable ();
  flag_sanity_graph := false;
  flag_sanity_env   := false;
  flag_sanity_disj  := false
(* Timing modules *)
let timing_apron:        bool ref = ref false
let timing_bshape:       bool ref = ref false (* base shape domain *)
let timing_fshape:       bool ref = ref false (* flat shape domain *)
let timing_lshape:       bool ref = ref false (* ad hoc list domain *)
let timing_pshape:       bool ref = ref false (* product shape domain *)
let timing_sshape:       bool ref = ref false (* sep shape domain *)
let timing_mem_exprs:    bool ref = ref false (* dom_mem_exprs *)
let timing_env:          bool ref = ref false
let timing_value:        bool ref = ref false
let timing_valset:       bool ref = ref false
let timing_graph_encode: bool ref = ref false
let timing_disj:         bool ref = ref false

(** Statistics *)
(* Count numbers of structures created *)
let stat_apron:        bool ref = ref false
