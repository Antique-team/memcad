(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_abs.mli
 **       experimental graph abstraction algorithm
 ** Xavier Rival, 2011/08/30 *)
open Graph_sig
open Nd_sig

(** Local graph abstraction routine *)
val graph_abs: hint_ug option -> (n_cons -> bool) -> graph -> graph
