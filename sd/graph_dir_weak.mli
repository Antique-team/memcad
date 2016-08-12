(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_dir_weak.mli
 **       experimental graph "graph directed weakening" algorithm
 **       - takes two arguments;
 **       - weakens only the second argument
 **       (the first one would be preserved as unroll)
 ** Xavier Rival, 2012/03/29 *)
open Data_structures
open Graph_sig
open Lib
open Nd_sig


(** Directed weakening function:
 **  - takes two arguments;
 **  - over-approximates only the right argument;
 **  - use the left argument as a "hint" of where to lose precision *)
val directed_weakening:
    graph (* left graph *)
  -> graph (* right graph *)
    -> (n_cons -> bool) (* right sat function *)
      -> hint_bg option (* optional hint *)
        -> node_wkinj (* node weak injection *)
          -> graph (* pre-initialized output *)
            -> graph * node_wkinj


(** Extraction of the mapping *)
val extract_mapping: graph -> node_wkinj -> unit node_mapping
