(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_algos.mli
 **       elements used for weakening algorithms on graphs
 ** Xavier Rival, 2012/04/10 *)
open Data_structures
open Graph_sig
open Ind_sig
open Nd_sig
open Set_sig

(** Sided algorithms support *)
(* Display *)
val side_2str: side -> string
(* Swap side *)
val other_side: side -> side
(* Side element extraction *)
val sel_side: side -> 'a * 'a -> 'a
val get_sides: side -> 'a * 'a -> 'a * 'a

(** Partial inclusion tests into inductive and segment edges *)

val is_le_ind:
    submem: bool (* sub-mem is_le is slightly different: no alloc check *)
  -> ind (* inductive definition to use for weakening *)
    -> graph (* graph to weaken *)
      -> int (* index of the node from which to weaken *)
        -> (n_cons -> bool) (* constraint verification *)
          -> (set_cons -> bool) (* set constraint verification *) 
            -> is_le_res * ind_edge * IntSet.t

val is_le_seg:
    submem: bool (* sub-mem is_le is slightly different: no alloc check *)
  -> ind (* inductive definition to use for weakening *)
    -> graph (* graph to weaken *)
      -> int (* source node from which to weaken *)
        -> int (* destination node up to which to weaken *)
          -> (n_cons -> bool) (* constraint verification *)
            -> (set_cons -> bool) (* set constraint verification *)
              -> is_le_res * seg_edge
