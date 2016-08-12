(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_visu.mli
 **       export graphs for visualization in the dot format for graphviz
 **       Francois Berenger and Huisong Li, 2015/02/24 *)
open Graph_sig

val pp_graph: string -> string list -> visu_option list
  -> graph -> namer -> out_channel -> unit
