(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_visu.mli
 **       functions for graphical output of lists
 ** Francois Berenger, started 2016/08/24 *)

open Graph_sig
open List_sig

val output_dot: visu_option list -> string -> string list -> lmem -> namer ->
  out_channel -> unit
