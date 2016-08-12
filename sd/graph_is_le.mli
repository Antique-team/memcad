(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_is_le.mli
 **       inclusion algorithm on graphs
 ** Xavier Rival, 2011/09/21 *)
open Data_structures
open Graph_sig
open Nd_sig

(** Inclusion check *)

(* The main function for inclusion testing:
 * used for checking stabilization of abstract iterates
 * 
 *  - stop:
 *    allows to use the liveness analysis results in order to guide the
 *    weakening process
 *)
val is_le:
    submem: bool (* sub-mem is_le is slightly different: no alloc check *)
  -> graph (* left input *)
    -> hint_ug option (* hint, in the left argument ("stop" nodes) *)
      -> (n_cons -> bool) (* satisfiability, in the left argument *)
        -> graph (* right input *)
          -> node_emb (* relation between both inputs *)
            -> int IntMap.t option (* extended relation if inclusion proved *)
              
(* Partial inclusion test:
 * used for weakening graphs (join, directed_weakening, graph_abs)
 * used for verifying assertions
 *
 *  - inst:
 *    nodes that can be instantiated are the integer parameters in the right
 *    hand side (they are used for weakening)
 *  - stop:
 *    allows to use the liveness analysis results in order to guide the
 *    weakening process
 *)
val is_le_partial:
    IntSet.t option (* nodes that might be instantiated at a later stage *)
  -> bool   (* whether to search for an inductive / a segment *)
    -> submem: bool (* sub-mem is_le is slightly different: no alloc check *)
      -> graph (* left input *)
        -> hint_ug option (* hint, in the left argument ("stop" nodes) *)
          -> IntSet.t (* segment end(s), if any *)
            -> (n_cons -> bool) (* satisfiability, in the left argument *)
              -> graph (* right input *)
                -> node_emb (* relation between both inputs *)
                  -> is_le_res (* generic iinclusion result *)
