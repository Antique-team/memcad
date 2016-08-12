(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_rules.mli
 **       symbolic path sound reduction rules
 ** Antoine Toubhans, 2012/04/19 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Constrain_sig

(* saturation function *)
val satur_null: id -> cstr -> cstr
val satur_eqs: id -> cstr -> cstr

val all_satur_null: cstr -> cstr
val all_satur_eqs: cstr -> cstr

(* tools for variable elimination *)
val modus_ponens_path: id -> cstr -> cstr
val modus_ponens_c_path: id -> cstr -> cstr
val modus_ponens_d_path: id -> cstr -> cstr

val all_modus_ponens_paths: cstr -> cstr
val all_modus_ponens_c_paths: cstr -> cstr
(* "forget_id id cstr" saturates constrains about id in cstr 
 * and then remove all constrains where id appears *)
val forget_id: id -> cstr -> cstr

(** reduction rules *)
(* rigidity rule: 
 * propagate equalities between 
 * targets of finite paths e.g. :
 *
 * SP |  Eq.cl: id[1]. { |1|,|2| }
 * SP |  Eq.cl: id[15]. { |17| }
 * SP |  Eq.cl: id[16]. { |9| }
 * ...
 * SP |  |2|.@{0}{1} |>> |3|
 * SP |  |1|.@{0}{1} |>> |17|
 * SP |  |1|.@{0}{1} |>> |9|  
 *
 * becomes:
 *
 * SP |  Eq.cl: id[1]. { |1|,|2| }
 * SP |  Eq.cl: id[15]. { |17|, |9| }
 * ...
 * SP |  |2|.@{0}{1} |>> |3|
 * SP |  |1|.@{0}{1} |>> |17|
 * SP |  |1|.@{0}{1} |>> |9|
 *)
val node_rigidity_rule: id -> node -> cstr -> cstr
val rigidity_rule: cstr -> cstr
(* eq. reducing rule: 
 * reduce ids that denote the same concrete
 * value, e.g. :
 *
 * SP |  Eq.cl: id[7]. { |2|, |3| }  
 * ...
 * SP |  |1|.@{0}{1} |>> |2|
 * SP |  |1|.@{0}{1} |>> |3|
 * SP |  |2|.@{0}{1} |>> |19|
 * SP |  |3|.@{0}{1} |>> |15|
 *
 * becomes:
 *
 * SP |  Eq.cl: id[7]. { |7| }  
 * ...
 * SP |  |1|.@{0}{1} |>> |7|
 * SP |  |7|.@{0}{1} |>> |19|
 * SP |  |7|.@{0}{1} |>> |15|   
 *
 * returns mapping:
 * |2| -> |7|
 * |3| -> |7|
 * ...
 * and reversed mapping:
 * |7| -> { |2|,|3| }
 * ...
 *)
val red_equalities: cstr -> cstr * (id, id PSet.t) PMap.t 

val simplify_paths: cstr -> cstr

(* c_path rules *)
val node_c_path_intro: id -> node -> cstr -> cstr
val fine_c_path_intro: id -> path -> path -> destination -> cstr -> c_path option
val c_path_intro: cstr -> cstr
val c_path_elim: cstr -> cstr

val node_path_c_path: id -> node -> cstr -> cstr
val path_c_path: cstr -> cstr 

(* d_path rules *)
val node_d_path_intro: id -> node -> cstr -> cstr

val d_path_intro: cstr -> cstr
val d_path_elim: cstr -> cstr

val node_path_d_path: id -> node -> cstr -> cstr
val path_d_path: cstr -> cstr 

val find_hint: id -> cstr -> (id * Offs.t PSet.t * id) list

(** reduction summary rules *)
(* maximum reduction: iteration of the above rules *)
val reduce: cstr -> cstr * (id, id PSet.t) PMap.t
