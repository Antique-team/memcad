(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_visu_sig.ml
 **       NODE and EGDE module signatures for graph output
 **       Francois Berenger, 2016/04/25 *)

open Data_structures
open Graph_sig

module type NODE =
  sig
    type t
    val create: node -> namer -> IntSet.t IntMap.t -> t
    val is_leaf: node -> bool
    val successors: node -> IntSet.t
    val successors_offs: node -> (step * int) list
    val is_inductive_src: t -> bool
    val to_string: IntSet.t -> t -> string
  end

type args = nid list * nid list * nid list

module type EDGE =
  sig
    type t =
      | Empty of nid
      | Inductive of string * nid * args
      | Segment of string * nid * args * Offs.OffSet.t * nid * args
      | Points_to of (nid * Offs.t * nid * Offs.t) list
    val of_node: node -> t
    val list_offsets: t list -> IntSet.t IntMap.t
    val to_string: t -> node IntMap.t -> string
  end
