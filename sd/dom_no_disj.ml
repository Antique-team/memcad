(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_no_disj.ml
 **       non disjunction replacement of the disjunction abstract domain
 ** Xavier Rival, 2011/09/05 *)
open Ast_sig
open Data_structures
open Dom_sig
open Dom_utils
open Flags
open Lib
open Graph_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "d_ndisj_" and level = Log_level.DEBUG end)

(** Functor lifting an environment domain into a disjunctive domain *)
module Dom_no_disj = functor (D: DOM_ENV) -> functor (GE: GRAPH_ENCODE) ->
  (struct
    let module_name = "dom_no_disj"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s -> %s\n%s%s"
        module_name D.module_name
        module_name GE.module_name
        (D.config_2str ())
        (GE.config_2str ())

    (* Abstract elements *)
    type t =
      | Bot       (* _|_ *)
      | Nb of D.t (* single disjunct *)

    (* Disjunction size *)
    let disj_size: t -> int = function
      | Bot  -> 0
      | Nb _ -> 1

    (* Commands *)
    type log_form = var tlval gen_st_log_form

    (* Bottom element *)
    let bot: t = Bot
    let is_bot: t -> bool = function
      | Bot -> true
      | Nb x -> D.is_bot x
    let remove_bot_disjuncts (u: D.t list): D.t list =
      List.filter (fun uu -> not (D.is_bot uu)) u
    (* Map functions *)
    let map (f: D.t -> D.t): t -> t = function
      | Bot -> Bot
      | Nb x -> Nb (f x)
    let map_list (f: D.t -> D.t list): t -> t list = function
      | Bot -> [ Bot ]
      | Nb x -> List.map (fun y -> Nb y) (f x)
    let map_one (f: D.t -> D.t list): t -> t = function
      | Bot -> Bot
      | Nb x ->
          match f x with
          | [ ] -> Bot
          | [ y ] -> Nb y
          | _ -> Log.fatal_exn "map_one"
    (* Top element, with provided set of roots *)
    let top (): t = Nb (D.top ())
    (* Pretty-printing *)
    let t_2stri (ind: string): t -> string = function
      | Bot -> Printf.sprintf "%s_|_" ind
      | Nb x -> D.t_2stri ind x
    let t_2str: t -> string = function
      | Bot -> "_|_"
      | Nb x -> D.t_2str x
    (* External output *)
    let ext_output (o: output_format) (base: string) (x: t): unit =
      match x with
      | Bot -> ( )
      | Nb u -> D.ext_output o base u
    (* Garbage collection *)
    let gc: t -> t = map D.gc

    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    let is_le (t0: t) (t1: t): bool =
      match t0, t1 with
      | Bot, _ -> true
      | Nb x0, Bot -> D.is_bot x0
      | Nb x0, Nb x1 -> D.is_le x0 x1
    (* Join and widening *)
    let merge_disjuncts (x: t): t = x
    let join (ho: hint_be option) (lo: (var lint_be) option)
        (t0: t) (t1: t): t =
      match t0, t1 with
      | Bot, _ -> t1
      | _, Bot -> t0
      | Nb x0, Nb x1 ->
          if !do_unary_abstraction then
            let hu = extract_hint ho in
            Nb (D.join ho lo
                  (D.local_abstract hu x0, ext_graph None None)
                  (D.local_abstract hu x1, ext_graph None None))
          else Nb (D.join ho lo (x0, ext_graph None None)
                     (x1, ext_graph None None))
    let widen (ho: hint_be option)  (lo: (var lint_be) option)
        (t0: t) (t1: t): t * t option =
      let res =
        match t0, t1 with
        | Bot, _ -> t1
        | _, Bot -> t0
        | Nb x0, Nb x1 ->
            if !do_unary_abstraction then
              let hu = extract_hint ho in
              Nb (D.widen ho lo (D.local_abstract hu x0, ext_graph None None)
                    (D.local_abstract hu x1, ext_graph None None))
            else Nb (D.widen ho lo (x0, ext_graph None None)
                       (x1, ext_graph None None)) in
      res, None
    let directed_weakening (ho: hint_be option) (t0: t) (t1: t): t =
      match t0, t1 with
      | Bot, _ | _, Bot -> t1
      | Nb x0, Nb x1 ->
          Nb (D.directed_weakening ho x0 x1)

    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    let assign (_: location) (lv: var tlval) (ex: var texpr): t -> t list =
      map_list (D.assign lv ex)
    (* Condition test *)
    let guard (_: location) (b: bool) (ex: var texpr) (t: t): t list =
      match t with
      | Bot -> [ Bot ]
      | Nb x ->
          (* reduction to _|_ *)
          let nx = D.guard b ex x in
          List.map (fun nu -> if D.is_bot nu then Bot else Nb nu) nx
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    let sat (ex: var texpr) (t: t): bool =
      match t with
      | Bot -> true
      | Nb x -> D.sat ex x

   (** set domain **)
   (* management of set vars *)
   let unary_op (op: unary_op) (x: t): t =
     match op with
     | UO_env eop -> map (D.unary_op eop) x
     | UO_ret _ -> Log.fatal_exn "return_var"
     | UO_mem (MO_alloc _ as mop) ->
         if !flag_malloc_never_null then map_one (D.memory mop) x
         else Log.fatal_exn "C malloc cannot be precisely analyzed w/o disj"
     | UO_mem (MO_dealloc _ as mop) -> map_one (D.memory mop) x

   let assume (op: state_log_form): t -> t = map (D.assume op)

   let check (op: state_log_form) (t: t): bool =
     match t with
     | Bot -> true
     | Nb x -> D.check op x

    (** Management of disjunctions *)
    (* Selective disjunct merge *)
    let sel_merge (_: var list) (ho: hint_be option)
        (lo: (var lint_be) option) (x: t): t =
      x
    (* Adding an abs_hist_atom *)
    let push_hist_atom (_: Disj_sig.abs_hist_atom) (x: t): t = x

    (** Analysis control *)
    (* Reduction + node relocalization *)
    let reduce_localize (lv: var tlval) (x: t): t =
      match x with
      | Bot -> Bot
      | Nb u ->
          match D.reduce_localize lv u with
          | None -> Bot
          | Some y -> Nb y
    (* Eager reduction *)
    let reduce_eager (x: t): t =
      match x with
      | Bot -> Bot
      | Nb y ->
          match D.reduce_eager y with
          | [] -> Bot
          | [u] -> Nb u
          | _ -> Log.fatal_exn "disjuncts out of reduce_eager"

    (** Assuming and checking inductive edges *)
    (* Unfold *)
    let ind_unfold (_: location)
        (u: Graph_sig.unfold_dir) (lv: var tlval): t -> t = function
      | Bot -> Bot
      | Nb x ->
          match remove_bot_disjuncts (D.ind_unfold u lv x) with
          | [ ] -> Bot
          | [ y ] -> Nb y
          | _ -> Log.fatal_exn "unfold in too many dijsuncts"

    (** Statistics *)
    (* For now, simply a number of disjuncts *)
    let get_stats: t -> int = function
      | Bot -> 0
      | Nb _ -> 1
  end: DOM_DISJ)
