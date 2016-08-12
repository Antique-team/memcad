(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_join.mli
 **       Graph join
 ** Xavier Rival, 2011/07/26 *)
open Data_structures
open Graph_sig
open Nd_sig
open Offs


(** The main graph join function *)
(* note: we miss something to try to discharge proof obligations! *)
val join:
    submem:bool (* whether to compute is_le for a sub-mem (no alloc check) *)
  -> graph * join_arg (* left graph *)
    -> (n_cons -> bool) (* left sat function *)
      -> graph * join_arg (* right input *)
        -> (n_cons -> bool) (* right sat function *)
          -> hint_bg option (* optional hint *)
            -> lint_bg option (* optional nullable node address *)
              -> node_relation (* relation between both inputs *)
                -> bool (* whether to NOT make roots prioretary *)
                  -> graph (* pre-computed, initial version of output *)
                    -> graph * node_relation * n_instantiation * n_instantiation
