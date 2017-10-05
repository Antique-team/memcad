(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_ppred_sig.ml
 **      signature of pure predicate: non inductive predicates
 ** Jiangchao Liu, 2016/8/8 *)
open Data_structures
open Lib

open Graph_sig
open Ind_sig
open Array_ind_sig
open Nd_sig
open Set_sig
open Sv_sig
open Svenv_sig


(* Types of rules *)
type prule_type =
  | PURE_EMPTY   (* empty rule *)
  | PURE_TRUE    (* numeric constraints on a set of cells *)
  | PURE_SINGLE  (* numeric constraints on a single cell *)


(* Definition of rules *)
type prule =
    { pr_type: prule_type;       (* type of rules *)
      pr_maya_cons: mform list;  (* maya constraints *)
      pr_n_cons: aform list; (* pure numeric constraints on scalar variables*) }


(* "Pure"  definition body *)
type p_def =
    { p_name: string;          (* name of def *)
      p_maya_offs: int list;   (* offsets of maya elements *)
      p_submem:    submem_ind; (* whether array cell is accessed by pointers *)
      p_rules: prule list;
      p_single_node: bool;     (* with empty and single *)
      p_ipars: int;            (* Parameters *) }


(* Memory state *)
type pmem =
    { pm_def:       p_def;
      pm_svemod:    svenv_mod;
      pm_mpar:      int option; (* is there an index for materialization *)
      pm_ipar:      int list; }

let ppred_defs: p_def StringMap.t ref = ref StringMap.empty

