(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_join.mli
 **       Join for the list domain
 ** Xavier Rival, 2014/03/04 *)
open Data_structures
open Graph_sig
open List_sig
open Nd_sig
open Set_sig

(* The main list join function *)
val join:
    lmem                     (* left graph *)
  -> (n_cons -> bool)        (* left sat function *)
  -> (set_cons -> bool)      (* left set sat function *)
  -> lmem                    (* right graph *)
  -> (n_cons -> bool)        (* right sat function *)
  -> (set_cons -> bool)      (* right set sat function *)
  -> hint_bg option          (* optional hint *)
  -> node_relation           (* initial node relation *)
  -> node_relation           (* initial set var relation *)
  -> bool                    (* whether to NOT make roots prioretary *)
  -> lmem                    (* pre-constructed output *)
  -> join_output             (* output *)
