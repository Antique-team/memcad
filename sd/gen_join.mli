(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: gen_join.mli
 **       Generic elements used in the join algorithm
 ** Xavier Rival, 2015/08/21 *)
open Data_structures

open Graph_sig
open Nd_sig

open Gen_dom

(** Kinds of rules in the join algorithm *)
type rkind =
  | Rpp | Rii         (* matching of pairs of pt/inductive edges *)
  | Rsegintro of side (* introduction of a segment *)
  | Rsegext           (* extension of a segment *)
  | Riweak            (* inductive in the left; weaken in the right graph *)
  | Rweaki            (* inductive in the right; weaken in the left graph *)
  | Rindintro         (* introduction of an inductive *)
  | Rsplitind of side (* seperate an inductive edge by introducing a segment *)
  | Rsegext_ext       (* extension of segments on both sides *)

(** Status, with set of applicable rules *)
type instances
type rules

(** Utilities and Pretty-printing *)
(* Empty set of applicable rules *)
val empty_rules: rules
(* Pretty-printing *)
val kind_2str: rkind -> string
val rules_2str: rules -> string

(** Strategy function, returning the next applicable rule *)
(* current strategy:
 *  1. pt-prio
 *  2. ind-ind
 *  3. seg-intro
 *  4. seg-ext
 *  5. weak-ind, ind-weak
 *  6. pt-pt
 *  7. ind-intro *)
val rules_next: rules -> (rkind * (int * int) * rules) option

(** Collecting applicable rules *)
val collect_rules_sv_gen:
    (int * int -> bool) (* whether pt rules are prioritary (init) *)
  -> bool             (* whether should be extension as segments*)
  -> bool             (* whether should be seg intro *)
    -> node_relation        (* node relation *)
      -> int -> region_kind  (* left node  *)
        -> int -> region_kind  (* right node *)
          -> rules -> rules

(** Invalidation of rules that were performed or disabled, by the application
 ** of another rule *)
(* Kinds of elements to invalidate *)
type invalid =
  | Ipt                (* a points to region *)
  | Iind               (* an inductive predicate *)
  | Inone              (* nothing *)
  | Iblob of IntSet.t  (* a memory blob *)
  | Isiblings          (* siblings of a node *)
(* Case of a local rule *)
val invalidate_rules:
    int -> int (* nodes *)
      -> invalid -> invalid (* what is becoming invalid *)
        -> rules -> rules

(** Extraction of mappings *)
val extract_mappings:
    IntSet.t -> IntSet.t
      -> Graph_sig.node_relation
        -> unit node_mapping * unit node_mapping

(** Specific functions *)
val rules_add_weakening: int * int -> rules -> rules
val rules_add_splitind_l: int * int -> rules -> rules
val rules_add_splitind_r: int * int -> rules -> rules
