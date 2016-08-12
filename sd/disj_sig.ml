(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: disj_sig.ml
 **       structures used in disjunction domains
 ** Xavier Rival, 2012/07/09 *)

(** Tokens on disjuncts
 **  This file defines path information that describes the origin of
 **  disjuncts, and may also help selecting which disjuncts to fold. *)

(** Location *)
(* => for now, line numbers
 *    but should eventually be replaced with more general locations *)
type loc = int

(** Unfold point *)
type h_unfold =
  | Uguard  (* @ guard statement *)
  | Uassign (* @ assign statement *)
  | Uunfold (* @ unfold statement *)

(** Abstract History atoms used for partitioning executions *)
type abs_hist_atom =
  (* Ah_if (l,b): b branch of cond at location l *)
  | Ah_if of loc * bool
  (* Ah_while l: true branch of the condition of loop at location l *)
  | Ah_while of loc
  (* Unfolding *)
  | Ah_unfold of h_unfold * loc * int

(** Abstract History: a stack of abstract history tokens *)
type abs_hist = abs_hist_atom list

(** List of abstract partitions *)
(* Denotes a function with a finite support *)
type 'a abs_hist_fun = (abs_hist * 'a) list
