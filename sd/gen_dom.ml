(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: gen_dom.ml
 **       General domain structures and algorithms
 ** Xavier Rival, 2014/03/08 *)


(** Structure used in is_le and join *)
(* Kinds of heap region; can be used by graph and list domains *)
type region_kind =
  | Kpt                (* a points to region *)
  | Kemp               (* an empty node *)
  | Kind               (* an inductive predicate *)
  | Kseg               (* a segment predicate *)
