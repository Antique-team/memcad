(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: rt_sig.ml
 **       signatures of the regression testing stuff
 ** Xavier Rival, 2011/09/29 *)
open Data_structures

(** Possible improvements:
 **  - change the type for options into a map, in order to make the
 **    parameterization code computing options in batch.ml a bit more
 **    systematic *)

type test_category =
  | TC_valid  (* validated test; should work *)
  | TC_wait   (* not validated yet; currently not ran *)
  | TC_exp    (* not validated yet; currently being worked on *)
  | TC_ignore (* ignored for now *)
  | TC_other of string (* other kind of test *)

(** Options to be passed to analysis *)
type test_spec =
    { (** Main input parameters *)
      (* source file, with path *)
      sp_src_file:   string;
      (* specific header for source file *)
      sp_header:     string;
      (* include dirs for C headers *)
      sp_idirs:     string;
      (* whether to use old parser *)
      sp_old_parser: bool;
      (* malloc never returns null *)
      sp_malloc_non0: bool;
      (* inductive file, with path *)
      sp_ind_file:   string;
      (* analysis of programs with recursive calls *)
      sp_auto_ind:   bool;
      (* ignore inductive prev fields upon graph encoding *)
      sp_no_prev_fields: bool;
      (* main function name *)
      sp_main_fun:   string;
      sp_rec_calls:  bool;
      (* automatic generation of inductive definitions *)
      (* whether to run in silent mode *)
      sp_silent:     bool;
      (* whether to run in very silent mode, for timing only *)
      sp_very_silent:bool;
      (* whether to run in verbose mode *)
      sp_verbose:    bool;
      (* setting/unsetting individual printing options *)
      sp_pp_add:     string list;
      sp_pp_rem:     string list;
      (* whether to dump domain individual operations (e.g., set domain) *)
      sp_dump_ops:   bool;
      (* time monitoring options *)
      sp_timing:     string list;
      (** Abstract domain: symbolic variables constraints *)
      (* numerical domain to use *)
      sp_numdom:     Flags.num_dom;
      (* whether to enable the sub-memory abstraction *)
      sp_submem:     bool;
      (* inductives for the sub-memory *)
      sp_subis:      StringSet.t;
      (* dynamic symbolic vars environment *)
      sp_dynenv:     bool;
      (* reduction mode *)
      sp_red_mode:   Flags.reduction_mode;
      (* set domain to use *)
      sp_setdom:     Flags.set_dom;
      (* Array domain *)
      sp_array:      bool;
      (* Equation pack *)
      sp_eq_pack:    bool;
      (** Abstract domain and inductive definitions *)
      (* whether to perform inductive definitions parameters analysis *)
      sp_indpars:    bool;
      (* structure of the shape domain to be used in the analysis *)
      sp_domstruct:  string;
      (** Iteration strategy, widening *)
      (* whether to use disjunctions *)
      sp_disj:       bool;
      (* whether to use the threshold widening *)
      sp_thrwide:    bool;
      (* widening steps to add *)
      sp_thrs:       IntSet.t;
      (* whether to use unary local abstraction (weak canonicalization) *)
      sp_unary_abs:  bool;
      (* unrolls *)
      sp_unrolls:    int;
      (* type unfolding *)
      sp_type_unfolds: int;
      (* directed weakening iterations *)
      sp_dirweak:    int;
      (* join iters *)
      sp_join_iters: int;
      (* whether to allow fast ind-ind rule *)
      sp_fast_iir:   bool;
      (* whether to partition inside while loops *)
      sp_part_lfps:  bool;
      (** Regression testing elements *)
      (* whether we should exclude this test
       * (temporary exclusion of non finished examples) *)
      sp_excluded:   bool;
      (* whether this test has already been validated:
       * if it fails, then it would be a regression *)
      sp_category:   test_category list;
      (* issue (if not working yet) *)
      sp_issue:      string;
      (* assertions (as appear in the end of the log) *)
      sp_assert_tot: int; (* total number *)
      sp_assert_ok:  int; (* validated assertions *)
      (* time out *)
      sp_time_out:   int;
      (* selection widen *)
      sp_sel_widen:  bool;
      (* basic widen *)
      sp_basic_widen:  bool;
    }

(* Test numbers with revision *)
module RevOrd =
  struct
    type t = int * char option
    let compare (i0,o0) (i1,o1): int =
      let ci = i0 - i1 in
      if ci != 0 then ci
      else
        match o0, o1 with
        | None, None -> 0
        | None, Some _ -> -1
        | Some _, None -> 1
        | Some ch0, Some ch1 -> int_of_char ch0 - int_of_char ch1
    let t_2str: t -> string = function
      | i, None -> Printf.sprintf "%d" i
      | i, Some c -> Printf.sprintf "%d%c" i c
  end
module RevMap = MapMake( RevOrd )
module RevSet = SetMake( RevOrd )
    
(* Collection of tests to perform
 *   integer -> character option -> test spec
 *   the "character option" is encoded as an integer
 *              -1 means "None"; i>=0 means (Some i) *)
type tests = test_spec RevMap.t


(** Test results *)
type test_success =
    { ts_assert_ok:  int;
      ts_assert_ko:  int;
      ts_time:       float; }
type test_result =
  | Tr_timeout
  | Tr_fail
  | Tr_ok of test_success
