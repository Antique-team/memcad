(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_sig.ml
 **       symbolic path language signatures
 ** Antoine Toubhans, 2012/04/19 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig

(* TODO:
 *  - normalize field names for eq_class, sp, gen_info *)


(** Type of abstract value **)
type id = int

(** Type for paths:
 ** a path is a reachability relation which contains  
 ** - a source: id
 ** - a path: a regexp with offset
 ** - a destination, either id or zero *)
type path = Offs.t Regular_expr.t

(* destination of a path *)
type destination = 
  | Pd_id of id (* abstract value *)
  | Pd_null     (* null pointer *)

(** type of equality classes **)
type eq_class =
    { (* set of abstract values equal to zero *)
      null_cl: id PSet.t;
      (* map from class identifier (int) to its class. *)
      cl: id PSet.t IntMap.t;
      (* next is the next available equality class identifier  *)
      next: int }
(* eq_loc, i.e. equality class identifier *)
type eq_cl_loc = 
  | Ecl_null
  | Ecl_id of int

(** c-path *)
type c_path = 
    { cp_targets: id PSet.t;
      cp_target_null: bool;
      cp_induc_path: path;
      cp_prop_path: path;
      cp_prop_dst: destination }

(** d-path *)
type d_path = 
    { dp_bw_target: id;
      dp_fw_induc: Offs.t PSet.t;
      dp_bw_induc: Offs.t;
      dp_targets: (id * id) PSet.t }

(** node **)
type node = 
    { (* eq class n belongs to *)
      n_eqs: eq_cl_loc;
      (* paths from n *)
      n_fw_paths: (path, destination PSet.t) PMap.t;
      (* on which nodes n appears as dest *)
      n_bw_paths: (path, id PSet.t) PMap.t;
      (* c_paths holding on the node *)
      n_c_paths: c_path PSet.t;
      (* node on wich n appears in c-paths *)
      n_bw_c_paths: id PSet.t;
      (* d_paths holding on the node *)
      n_d_paths: d_path PSet.t;
      (* node on wich n appears in c-paths *)
      n_bw_d_paths: id PSet.t;
      (* flag: node != null *)
      n_not_null: bool; }

(** symbolic path language **)
type cstr =
    { (* mapping from id to its node *)
      nodes: (id, node) PMap.t;
      (* equivalence classes *)
      eq_class: eq_class;
      (* id env infos *)
      id_up: id;
      id_free: id list }

(* for inductive predicate extraction *)
type cstr_indcall =
    { cstri_cstr:    cstr;
      (* main entry point *)
      cstri_main: id;
      (* entry points for ptr parameters *)
      cstri_ppars: id list; 
      (* entry points for int parameters *)
      cstri_ipars: id list }

(* for segment predicate extraction *)
type cstr_segcall =
    { cstrs_cstr:    cstr;
      (* source entry point *)
      cstrs_src: id;
      (* entry points for source ptr parameters *)
      cstrs_sppars: id list; 
      (* entry points for source int parameters *)
      cstrs_sipars: id list;
      (* destination entry point *)
      cstrs_dst: id;
      (* entry points for dst ptr parameters *)
      cstrs_dppars: id list; 
      (* entry points for dst int parameters *)
      cstrs_dipars: id list }


(* mapping, used for join operation *)
type id_mapping = 
    { (* mapping from the left part to the new cstr *)
      nm_left: (id, id) PMap.t;
      (* mapping from the right part to the new cstr *)
      nm_right: (id, id) PMap.t;
      (* mapping from the new cstr to the two parts *)
      nm_rev: (id, (id * id)) PMap.t }

(** types for ind/seg pre-analysis **)
type status = 
  (* Unsound: keep going *)
  | Unsound
  (* Sound: a sound invariant has been found,
   * it can be used to discover other invariant *)
  | Sound
  (* Killed: the process has been stopped for some reasons 
   * - either dependancies can't be resolved 
   *   cycle dependancies for instance 
   * - number of iteration geq than Flag.max_pre_analysis_iter *)
  | Killed

(* Type for collecting data when computing an ind/seg invariant *)
type 'a gen_info = 
    { n_ipars: int;
      n_ppars: int;
      status: status;
      (* depends on which other inductive definitions *)
      depends: StringSet.t;
      (* cstr computed at this point *)
      ocstr: 'a option;
      (* terminal rule: do not contain call to itself *)
      term_rules: Ind_sig.irule list;
      (* non terminal rule *)
      no_term_rules: Ind_sig.irule list }

type ind_info = cstr_indcall gen_info
type seg_info = cstr_segcall gen_info

