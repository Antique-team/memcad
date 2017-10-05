(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_utils.mli
 **       utilities for the abstract domain
 ** Xavier Rival, 2011/10/17 *)
open Data_structures

open Ast_sig
open Dom_sig
open Ind_sig
open Sv_sig
open Svenv_sig
open Graph_sig

(** Basic pretty-printing *)
val join_kind_2str: join_kind -> string

(** Map functions over gen_ind_call *)
val map_gen_ind_call: ('a -> 'b) -> ?g:(setvar -> int) -> 'a gen_ind_call
  -> 'b gen_ind_call

(** Emptiness test on gen_ind_call *)
val gen_ind_call_is_empty: 'a gen_ind_call -> bool

(** Hints for domain operators *)
val extract_hint: hint_be option -> hint_ue option

(** Renaming operations *)
(* Pretty printing *)
val renaming_2stri: string -> int IntMap.t -> string
(* Composition of renamings:
 *   - a renaming r is represented by a map M_r such that
 *     r(i) = M_r(i) if i \in M_r
 *     r(i) = i      otherwise
 *   - composition is defined as usual: (r0 o r1)(i) = r0(r1(i))
 *)
val renaming_compose: int IntMap.t -> int IntMap.t -> int IntMap.t

(** Envmod structure *)
val svenv_empty: svenv_mod
val svenv_is_empty: svenv_mod -> bool
val svenv_2stri: string -> svenv_mod -> string
(* removal of an SV *)
val svenv_rem: int -> svenv_mod -> svenv_mod
val svenv_add: int -> ntyp -> svenv_mod -> svenv_mod
val svenv_join: svenv_mod -> svenv_mod -> svenv_mod
(* Mapping function used in dom_mem_low_prod/sep *)
val svenv_map: (int -> int) -> svenv_mod -> svenv_mod
(* generic application of modifications in an svenv_mod *)
val svenv_mod_doit: (int -> ntyp -> 'a -> 'a) -> (int -> 'a -> 'a)
  -> (int -> 'a -> 'a) -> svenv_mod -> 'a -> 'a

(** Symbolic variable environment updater *)
val sv_upd_2set: sv_upd -> IntSet.t
val sv_upd_2str: sv_upd -> string
val svenv_upd_empty: svenv_upd
val svenv_upd_identity: svenv_upd
val svenv_upd_embedding: unit Nd_sig.node_mapping -> svenv_upd

(*extending the joining graph with its encoding *)
val ext_graph: abs_graph option ->  abs_graph option -> join_ele

