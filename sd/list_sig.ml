(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_sig.ml
 **       signatures of a simplified inductive domain based on lists
 **       (no parameters, no arbitrary inductives)
 ** Xavier Rival, 2014/02/23 *)
open Data_structures
open Lib

open Graph_sig
open Ind_sig
open Nd_sig
open Set_sig
open Sv_sig
open Svenv_sig

(** The purpose of this domain is to implement a simplified version of
 ** the general inductive definition based abstract domain, and to serve
 ** for experimentation. *)


(** Set predicates *)

(* Variables in constraints, that denote set elements *)
type set_elt =
  | Se_this         (* address of the current object *)
  | Se_field of int (* contents of a field of offset i *)

(* Variables in constraints, that denote sets, in the context of an inductive
 * definition; those variables refer to parameters:
 *  - actual parameters (of the current call)
 *  - next parameter (of the call corresponding to the tail of the list)
 *  - sub-parameter (of a call corresponding to a nested list) *)
type set_var =
  | Sv_actual of int  (* i-th actual parameter ---E_i *)
  | Sv_nextpar of int (* i-th parameter of next call ---E'_i *)
  | Sv_subpar of int * int (* i-th parameter of j-th sub-call ---E^j_i *)

(* Expressions defining a set, in the context of the inductive definition *)
type set_def =
  | Sd_var of set_var              (* X *)
  | Sd_uplus of set_elt * set_var  (* {y} \uplus X *)
  | Sd_eunion of set_elt * set_var (* {y} \union X *)
  | Sd_union of set_var * set_var  (* X \union Y *)

(* Constraints over sets, in the context of the inductive definition *)
type set_equa =
  | Se_mem of set_elt (* i0 *) * set_def (* s1 *)    (* i0 \in s1 *)
  | Se_eq  of set_var (* s0 *) * set_def (* s1 *)    (* s0 = s1 *)

(* Set part to a "list" inductive definition *)
type seti =
    { (* set parameter kinds *)
      s_params:  set_par_type list; (* const/head/add *)
      (* parameter used for unfolding an indutive to a segment and an
       * inductive edge *)
      s_uf_seg:  int option;
      (* set constraints associated to the definition *)
      s_equas:   set_equa list }


(** Abstract elements *)

(* "List" inductive definition body *)
type l_def =
    { ld_name:    string option; (* name of the ind. def. it derives from *)
      ld_nextoff: int;           (* offset of the next field (list tail ptr) *)
      ld_size:    int;           (* size of the block describing an element *)
      ld_onexts:  (int * l_def) list; (* nested lists (if any) *)
      ld_set:     seti option;   (* set constraints (if any) *) }

(* "List" inductive predicate, with parameters *)
type l_call =
    { lc_def:   l_def;   (* definition (induction scheme) *)
      lc_args:  int list (* arguments; list of SETVs *) }

(* Kinds of heap fragments for a node (very similar to graph) *)
type lheap_frag =
  | Lhemp                        (* empty (no memory) *)
  | Lhpt of pt_edge Block_frag.t (* block *)
  | Lhlist of l_call             (* complete list *)
  | Lhlseg of l_call * nid       (* segment of a list *)

type lnode =
    { ln_i:     nid;          (* node id *)
      ln_e:     lheap_frag;   (* memory block at this address *)
      ln_typ:   ntyp;         (* type *)
      ln_odesc: l_def option; (* desc that node may have had in the past *) }

(* SV invariants:
 *  - svemod holds already performed local changes
 *  - prerem SVs are not reachable and ready to be disposed of
 *  - nkey holds SVs that are allocated (could be in prerem)
 *)
type lmem =
    { (* Memory state *)
      lm_mem:       lnode IntMap.t;
      (* Managemeng of SVs *)
      lm_nkey:      Keygen.t; (* key allocator for the symbolic variables *)
      lm_roots:     IntSet.t;
      lm_svemod:    svenv_mod;
      (* Dangling SVs: neither root nor referenced somewhere else *)
      lm_dangle:    IntSet.t;
      (* Management of SETVs *)
      lm_setvkey:   Keygen.t; (* key allocator for the set variables *)
      lm_setvroots: IntSet.t; (* setv which are root *)
      lm_setvkind:  set_par_type IntMap.t; (* kind of setvs *)
      (* GC management by ref counting and prev pointers;
       *  - lm_refcnt stores a map of the form
       *               node => prev => number of occurences
       *                               of "node" as a successor of prev *)
      lm_refcnt:    int IntMap.t IntMap.t; }


(** Unfolding algorithm result *)

type unfold_result =
    { ur_lmem:     lmem;
      ur_cons:     n_cons list;           (* num constraints, to integrate *)
      ur_setcons:  set_cons list;         (* set constraints, to integrate *)
      ur_newsetvs: set_par_type IntMap.t; (* set of new setvs *)
      ur_remsetvs: IntSet.t;              (* set of removed setvs *) }


(** Partial inclusion checking algorithm output *)

(* Ilr_not_le:  failed to establish inclusion
 * Ilr_le:      success, with node mapping right to left
 * and set variable mapping from right to left, set domian
 * in right side, and some unfold set info to help implication prove
 * Ilr_le_rem:  success on a sub-abstract memory, with remainder
 *)
type is_le_ym = (* yes or maybe comparison *)
  [ `Ilr_le of (int IntMap.t) * (IntSet.t IntMap.t) * (set_cons list)
  | `Ilr_not_le ]
type is_le_weaken_check = (* checking a weakening (join) *)
  [ `Ilr_le_rem of lmem   (* the remainder in the left hand side *)
      * IntSet.t          (* nodes removed in the left hand side *)
      * (int IntMap.t)
      * (IntSet.t IntMap.t)
      * set_cons list   (* un-discharged, un-renamed right set constraints *)
  | `Ilr_not_le ]
type is_le_weaken_guess =
  [ `Ilr_le_list of lmem * (int IntMap.t) * (IntSet.t IntMap.t)
        * (set_cons list)                          (* remainder *)
  | `Ilr_le_lseg of lmem                                (* remainder *)
        * int * (int IntMap.t) * (IntSet.t IntMap.t) 
        * (set_cons list)                          (* end-point *)
  | `Ilr_not_le ]


(** Join algorithm output *)

type join_output =
   { (* output shape domain*)
     out:       lmem;
     (* relation between outputs and inputs *)
     rel:       node_relation;
     (* set constraints to use in the instantiation *)
     instset_l: Inst_sig.setv_inst;
     instset_r: Inst_sig.setv_inst; }
