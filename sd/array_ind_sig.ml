(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_ind_sig.ml
 **       data-types for the inductive definitions.
 ** Jiangchao Liu, 2011/06/29 *)

open Data_structures
open Ast_sig
open Sv_sig
open C_sig
open Ind_sig


type formal_maya_arg =
  | Fa_par_maya of int (* maya type parameter *)
  | Fa_par_nmaya of int (* fresh maya type parameter *)

(** Parameters in inductive calls *)
(* Occurrence of a variable in an inductive
 * we use various types, depending on the position of the occurence *)
type ai_formal_arg =
  | Formal_arg of formal_arg
  | Maya_arg of formal_maya_arg

type formal_maya_args = formal_maya_arg list

(* maya formula *)
type mform =
  | Ai_Mf_mem of formal_arith_arg * formal_maya_arg  (* membership *)
  | Ai_Mf_equal_s of formal_maya_arg * formal_maya_arg  (* equality *)
  | Ai_Mf_cons of c_binop * formal_maya_arg * aexpr  (* arithmetric equality *)
  | Ai_Mf_included of formal_maya_arg * formal_maya_arg   (* including *)
  | Ai_Mf_empty of formal_maya_arg                   (* emptiness *)
  | Ai_Mf_cardinality of formal_maya_arg * int  (* cardinality of a set *)

(* pure formula *)
type ai_pformatom =
  | Ai_Pf of pformatom
  | Ai_Pf_maya of mform (* maya predicates *)

type ai_pform = ai_pformatom list (* conjunction *)

(** Rules *)
(* Rule kind *)
type air_kind =
  | Aik_unk         (* unknown type (no hint available for this rule) *)
  | Aik_true        (* no predicate, only used for array predicate*)
  | Aik_empi        (* empty heap, ptr is not null, only for array predicate *)

(* Rule of an inductive definition *)
type airule =
    { (** Components of the rule *)
      air_num:  int;           (* number of new SVs *)
      air_typ:  ntyp IntMap.t; (* types of the new variables *)
      air_heap: hform;         (* heap part *)
      air_pure: ai_pform;      (* pure part *)
      air_kind: air_kind;      (* kind of the rule *)
      (** Elements derived by inductive definition analysis *)
      air_unone: bool;         (* true iff it uses no parameter at all *) }

type access =
  | Access_by_offset
  | Access_by_pointer

type submem_ind =
    { acc_type: access;
      groups:   int;}

(** Inductive definitions *)
type array_ind =
    { (** Components of the definition *)
      ai_submem:  submem_ind option;
      (* Whether this is a inductive for submemory*)
      ai_name:    string;     (* name *)
      ai_ppars:   int;        (* number of int parameters *)
      ai_ipars:   int;        (* number of ptr parameters *)
      ai_mpars:   int list;   (* offsets of maya parameters *)
      ai_rules:   airule list; (* rules *)
      (** Elements that should help the analysis (derived by ind. analysis) *)
      ai_mt_rule: bool;      (* existence of a rule with null ptr, emp heap *)
      ai_emp_ipar: int;      (* existence of rule with emp heap and int param *)
    }

