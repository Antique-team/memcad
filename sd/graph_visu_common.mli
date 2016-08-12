(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_visu_common.mli
 **       functions common to graphs and encoded graphs output
 ** Francois Berenger and Huisong Li, started 2015/02/24 *)

open Data_structures
open Graph_sig

val get_name: namer -> int -> string
val successors_only: StringSet.t -> graph -> namer -> IntSet.t
val filter_nodes: IntSet.t -> graph -> graph
