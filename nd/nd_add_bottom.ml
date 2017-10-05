(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_add_bottom.ml
 **       addition of a bottom element to a numerical domain
 ** Xavier Rival, 2011/07/03 *)
open Data_structures
open Lib
open Nd_sig

module Log =
  Logger.Make(struct let section = "nd_+bot_" and level = Log_level.DEBUG end)

(** Functor adding a bottom element to a numerical domain *)
module Add_bottom = functor (D: DOM_NUM_NB) ->
  (struct
    let module_name = "nd_add_bot"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name D.module_name (D.config_2str ())
    type t =
      | Bot
      | Nb of D.t
    (* Lift operator, for internal use, and code concision,
     * works for all _|_-strict functions *)
    let lift (f: D.t -> D.t): t -> t = function
      | Bot as x -> x
      | Nb t -> Nb (f t)

    (* Bottom element *)
    let bot = Bot
    let is_bot: t -> bool = function
      | Bot  -> true
      | Nb t -> D.is_bot t
    (* Top element *)
    let top = Nb D.top
    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string): t -> string = function
      | Bot -> Printf.sprintf "%sBOTTOM\n" ind
      | Nb t -> D.t_2stri sn ind t
    (* Variables management *)
    let add_node i = lift (D.add_node i)
    let rem_node i = lift (D.rem_node i)
    let vars_srename (nr: 'a node_mapping) = lift (D.vars_srename nr)
    let check_nodes (s: IntSet.t): t -> bool = function
      | Bot -> true
      | Nb t -> D.check_nodes s t
    let nodes_filter (nkeep: IntSet.t): t -> t = lift (D.nodes_filter nkeep)

    (** Comparison and Join operators *)
    let is_le (x0: t) (x1: t) (sat_diseq: int -> int -> bool): bool =
      match x0, x1 with
      | Bot, _ -> true
      | _, Bot -> is_bot x0
      | Nb t0, Nb t1-> D.is_le t0 t1 sat_diseq
    let join (x0: t) (x1: t): t =
      match x0, x1 with
      | Bot, x -> x
      | x, Bot -> x
      | Nb t0, Nb t1 -> Nb (D.join t0 t1)
    let widen (x0: t) (x1: t): t =
      match x0, x1 with
      | Bot, x -> x
      | x, Bot -> x
      | Nb t0, Nb t1 -> Nb (D.widen t0 t1)

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (c: n_cons): t -> bool = function
      | Bot -> true
      | Nb t -> D.sat c t

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr): t -> t = lift (D.assign dst expr)
    let guard (b: bool) (c: n_cons) (x: t): t =
      try lift (D.guard b c) x with Bottom -> Bot

    (** Utilities for the abstract domain *)
    let simplify_n_expr (t: t) (e: n_expr): n_expr =
      match t with
      | Bot -> e
      | Nb t0 -> D.simplify_n_expr t0 e

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another  *)
    let expand (id: int) (nid: int): t -> t = lift (D.expand id nid)
    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int): t -> t = lift (D.compact lid rid)

    (** Conjunction *)
    let meet (lx: t) (rx: t): t =
      match lx, rx with
      | Bot,_ -> Bot
      | _,Bot -> Bot
      | Nb l,Nb r -> Nb (D.meet l r)

    (** Forget the information on a dimension *)
    let sv_forget (id: int): t -> t = lift (D.sv_forget id)

    (** Export of range information *)
    (* bound of a variable  *)
    let bound_variable (dim: int) (x: t): interval =
      match x with
      | Bot -> { intv_inf = None;
                 intv_sup = None }
      | Nb y -> D.bound_variable dim y

    (** Extract the set of all SVs *)
    let get_svs (x: t): IntSet.t =
      match x with
      | Bot -> IntSet.empty
      | Nb y -> D.get_svs y

    (** Extract all SVs that are equal to a given SV  *)
    let get_eq_class (i: int) (x: t): IntSet.t =
      match x with
      | Bot -> IntSet.empty
      | Nb y -> D.get_eq_class i y
  end: DOM_NUM)
