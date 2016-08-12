(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_materialize.mli
 **       unfolding of graphs, materialization
 ** Xavier Rival, 2011/08/06 *)
open Data_structures
open Graph_sig
open Ind_sig
open Nd_sig

(** Materialization of one rule *)
(* returns:
 * - unfolded graph
 * - additional constraints
 * - set of new nodes *)
val materialize_rule:
    submem: bool (* whether sub-memory is_le (no alloc check) *)
  -> nid -> ind -> ind_args
    -> (nid * ind_args) option
      -> bool (* whether segment of length 1 (segment case) *)
        -> irule -> graph
          -> (graph * PairSet.t) list * n_cons list * IntSet.t
              
(** Materialization of an inductive *)
(* returns a list of tuples of the same form as for materialize_rule *)
val materialize_ind:
    submem: bool (* whether sub-memory is_le (no alloc check) *)
  -> bool option (* whether to put empty rules first, last or not to care *)
    -> bool (* whether to generate empty segment case (for segment unfold) *)
      -> bool (* whether segment is of length 1 (for segment unfold) *)
        -> int -> graph -> unfold_res list

(** Higher level unfold function *)
val unfold:
    submem: bool (* whether sub-memory is_le (no alloc check) *)
  -> int (* source: node where unfolding should take place *)
    -> unfold_dir (* direction, for segment edges only *)
      -> graph    (* input graph *)
        -> unfold_res list
