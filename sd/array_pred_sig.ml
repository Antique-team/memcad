(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_pred_sig.ml
 **       signature of array predicates
 ** Jiangchao Liu, 2015/11/29 *)
open Data_structures
open Ast_sig

(* XR: not enough comments on constructors, for instance on:
 *  - atom_compred
 *  - compred, numpred, apred
 *)

(* identifiers: Current index and the successor *)
type ident =
  | Acur
  | Asucc

(** predicates (string) from parser *)
(* hint_array stores predicates to be checked, we call it hint_array since
 * it helps us in re-group strategy *)
let hint_array: string ref = ref ""
    
(* assume_array stores predicates assumed  *)
let assume_array: string ref = ref ""

(* arithmetic operators *)
type a_arbop =
  | Abadd | Absub | Abmul | Abmod
  
(* compare operators *)
type a_combop = 
  | Abne | Abeq | Abge | Abgt | Able | Ablt 

(* logical operators *)
type a_logbop =
  | Abland | Ablor 

(* program var *)
type avar = 
  | Unrv_var of string
  | Rv_var of int
  | Harv_var of var

(* offset *)
type aoff =
  | Unrv_off of string
  | Rv_off of int

(* left value *)
type alval =
  | Avar of avar
  | Aident of ident
  | Aarray_strut of avar * alval * aoff
  | Aarray of avar * alval

(* expression *)
type aexpr =
  | Aelval of alval
  | Aeconst of int
  | Aminus of  aexpr
  | Aebin of a_arbop * aexpr * aexpr

(* condition test  *)
type acond = 
  | Arith of a_combop * aexpr * aexpr
  | Logic of a_logbop * acond * acond

(* Compositional predicates *)
type atom_compred = 
    { head:     aexpr;
      succ:     aexpr;
      exitcond: acond; }

type compred = atom_compred list
    
(* Arithmetic form predicates *)
type numpred = 
    { var:      ident;
      assum:    acond;
      solution: acond; }

(* Array predicates *)
type apred =
  | Nump of numpred
  | Comp of compred

(* TODO XR => JL: no comment on this interface... *)
module type ARRAY_PREDICATE = 
  sig
    type t 
    type gd
    val t_2stri: string -> t -> string
    val rename: int -> int -> int -> gd -> t -> gd -> t -> gd * t * gd * t
    val materialize:(int * int, int) Bi_fun.t -> int -> gd -> t -> gd * t 
    val joinrank: int -> int -> t -> int
    val rem_all_predicates: gd -> t -> gd * t
    val assign_simple:(int * int, int) Bi_fun.t -> int -> gd -> t -> gd * t
    val pred_check: (int * int, int) Bi_fun.t-> gd -> t -> bool
    val merge: int -> int -> gd -> t  -> gd * t
    val is_applicable: apred -> bool
    val initialize: apred -> t
    val is_incl_group: int -> int -> t -> t -> bool
  end

