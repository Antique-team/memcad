(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: gen_is_le.mli
 **       Generic elements used in the inclusion checking algorithm
 ** Xavier Rival, 2015/08/21 *)
open Data_structures

open Gen_dom

(** Exception when inclusion fails be checked *)
exception Le_false of string

(** Rules that could be applied right away *)
(* Kinds of rules *)
type rkind =
  (* Reaching a stop node *)
  | Rstop
  (* Siblings, detection of void segments *)
  | Rvs
  (* Conventional pair of edges *)
  | Rpp | Rii | Rss | Rsi | Rei | Rpi | Rps
(* Record of rules that can be activated *)
type instances
type rules

(** Utilities and Pretty-printing *)
(* Empty set of applicable rules *)
val empty_rules: rules
(* Pretty-printing *)
val rkind_2str: rkind -> string
val rules_2str: rules -> string

(** Strategy function; returns next rule to apply *)
(* current strategy:
 *  0. stop (exit)
 *  1. pt-prio
 *  2. ind-ind, seg-seg, seg-ind
 *  3. pt-seg, pt-ind
 *  4. pt-pt
 *  5. emp-ind, emp-seg
 * this is basically the big selector... *)
val rules_next: rules -> (rkind * (int * int) * rules) option

(** Collecting applicable rules *)
val collect_rules_sv_gen:
    (int -> 'a -> region_kind) (* get the kind of an SV edge *)
  -> (int -> 'a -> int option) (* get segment ends *)
    -> bool (* whether pt rules are prioritary (init) *)
      -> (int Aa_sets.t option) (* optional hint ("stop" nodes) *)
        -> (IntSet.t) (* optional end of segment points *)
          -> (Graph_sig.node_embedding) (* mapping, used to guess siblings *)
            -> 'a -> 'a (* left and right arguments *)
              -> int -> int (* SVs *)
                -> rules -> rules

(** Invalidation of rules that were performed or disabled, by the application
 ** of another rule *)
val invalidate_rules:
    int -> int (* SVs *)
      -> region_kind -> region_kind (* kinds *)
        -> rules -> rules
        



