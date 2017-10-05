(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_add_diseqs.ml
 **       addition of equalities to a numerical domain
 **         (without bottom interface)
 ** Xavier Rival, 2011/08/08 *)
open Apron
open Data_structures
open Lib
open Nd_sig
open Nd_utils

module Log =
  Logger.Make(struct let section = "nd_+eq" and level = Log_level.DEBUG end)


(** Equalities are represented using union finds over atoms *)
let rem_atom (at: atom) (au: atom Union_find.t): atom Union_find.t =
  if Union_find.mem at au then
    let _,te = Union_find.rem at au in te
  else au

let union_atom (at: atom) (r: atom) (au: atom Union_find.t)
    : atom Union_find.t =
  let re, au =
    if Union_find.mem r au then
      Union_find.find r au
    else
      r, Union_find.add r au in
  let ae, au =
    if Union_find.mem at au then
      Union_find.find at au
    else
      at, Union_find.add at au in
  Union_find.union re ae au

let add_atom (at: atom) (r: atom) (au: atom Union_find.t): atom Union_find.t =
  let au = rem_atom at au in
  union_atom at r au


(** Module adding disequality constraints on top of another numerical domain *)
module Add_eqs = functor (M: DOM_NUM_NB) ->
  (struct
    let module_name = "nd_add_seqs"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name M.module_name (M.config_2str ())

    type t =
        { t_u: M.t ;              (* underlying: equalities, inequalities *)
          t_e: atom Union_find.t  (* disequalities *) }

    (* Bottom element (might be detected) *)
    let is_bot (t: t): bool =
      (* Conflicting equalities and disequalities get reduced to _|_
       *  incrementally, via "raise Bottom" *)
      M.is_bot t.t_u

    (* Top element *)
    let top: t =
      { t_u = M.top ;
        t_e = Union_find.empty }

    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string) (t: t): string =
      let seqs = Union_find.t_2stri "" (atom_2str sn) t.t_e in
      Printf.sprintf "%s%s" seqs (M.t_2stri sn ind t.t_u)

    (* Variables managemement *)
    let add_node (i: int) (t: t): t =
      { t with t_u = M.add_node i t.t_u }
    let rem_node (i: int) (t: t): t =
      { t_u = M.rem_node i t.t_u;
        t_e = rem_atom (Anode i) t.t_e }

    (* Renaming *)
    let vars_srename (nr: 'a node_mapping) (t: t): t =
      let af_rem =
        IntSet.fold (fun key -> rem_atom (Anode key)) nr.nm_rem t.t_e in
      let af_map =
        IntMap.fold
          ( fun key (el,set) acc ->
            if Union_find.mem (Anode key) acc then
              let acc = Union_find.var_rename (Anode key) (Anode el) acc in
              let rep,_ = Union_find.find (Anode el) acc in
              IntSet.fold
                ( fun key iac ->
                  if Union_find.mem (Anode key) iac then iac
                      else Union_find.add (Anode key) ~rep:rep iac
                 )  set acc
            else
              acc
           )nr.nm_map af_rem in
      { t_u = M.vars_srename nr t.t_u ;
        t_e = af_map }
    let check_nodes (s: IntSet.t) (t: t): bool =
      M.check_nodes s t.t_u
    let nodes_filter (nkeep: IntSet.t) (t: t): t =
      (* ljc: incomplete *)
      { t_u = M.nodes_filter nkeep t.t_u ;
        t_e = t.t_e }

    (** Comparison, Join and Widening operators *)
    let is_le (t0: t) (t1: t) (f: int -> int -> bool): bool =
      M.is_le t0.t_u t1.t_u f
    let join (t0: t) (t1: t): t =
      { t_u = M.join t0.t_u t1.t_u ;
        t_e = Union_find.meet t0.t_e t1.t_e }
    let widen (t0: t) (t1: t): t =
      { t_u = M.widen t0.t_u t1.t_u ;
        t_e = Union_find.meet t0.t_e t1.t_e }

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (cons: n_cons) (t: t): bool =
      match cons with
      | Nc_cons (Tcons1.DISEQ, Ne_var vi, Ne_csti ci)
      | Nc_cons (Tcons1.DISEQ, Ne_csti ci, Ne_var vi) ->
           not (Union_find.is_same_class (Acst ci) (Anode vi) t.t_e)
            && M.sat cons t.t_u
      | Nc_cons (Tcons1.DISEQ, Ne_var v0, Ne_var v1) ->
          not (Union_find.is_same_class (Anode v0) (Anode v1) t.t_e)
            && M.sat cons t.t_u
      | _ -> (* send to underlying domain *)
          M.sat cons t.t_u

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr) (t: t): t =
      let te =
        match expr with
        | Ne_var i ->
            add_atom (Anode dst) (Anode i) t.t_e
        | Ne_csti c ->
            add_atom (Anode dst) (Acst c) t.t_e
        |  _ -> rem_atom (Anode dst) t.t_e in
      { t_u = M.assign dst expr t.t_u ;
        t_e = te }
    let guard (b: bool) (cons: n_cons) (t: t): t =
      assert b;
      (* simplification on offset expressions *)
      let cons = Nd_utils.n_cons_simplify cons in
      match cons with
      | Nc_cons (Tcons1.DISEQ, Ne_var v0, Ne_var v1) ->
          (* Incremental reduction:
           *  -> if the equality is trivially satisfied or satisfied in num,
           *     then we reduce to _|_ immediately *)
          if v0 = v1 then raise Bottom
          else if sat (Nc_cons (Tcons1.EQ, Ne_var v0, Ne_var v1)) t then
            raise Bottom
          else
            { t with t_u = M.guard b cons t.t_u }
      | Nc_cons (Tcons1.DISEQ, Ne_var vi, Ne_csti ci)
      | Nc_cons (Tcons1.DISEQ, Ne_csti ci, Ne_var vi) ->
          (* Incremental reduction:
           *  -> if the equality is satisfied in the num domain, we
           *     reduce to _|_ immediately *)
          if sat (Nc_cons (Tcons1.EQ, Ne_var vi, Ne_csti ci)) t then
            raise Bottom
          else
            { t with t_u = M.guard b cons t.t_u }
      | Nc_cons (Tcons1.EQ, Ne_var v0, Ne_var v1) ->
          { t_u = M.guard b cons t.t_u;
            t_e = union_atom (Anode v0) (Anode v1) t.t_e }
      | Nc_cons (Tcons1.EQ, Ne_var v0, Ne_csti c0)
      | Nc_cons (Tcons1.EQ, Ne_csti c0, Ne_var v0) ->
          { t_u = M.guard b cons t.t_u;
            t_e = union_atom (Anode v0) (Acst c0) t.t_e }
            (* new case: reduction "e0 >= e1" to "e0 > e1" *)
      | _ ->
          { t with t_u = M.guard b cons t.t_u }

    (** Utilities for the abstract domain *)
    let simplify_n_expr (t: t): n_expr -> n_expr = M.simplify_n_expr t.t_u

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    let expand (id: int) (nid: int) (x: t): t =
      { x with t_u = M.expand id nid x.t_u }
    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int) (x: t): t =
      { x with t_u = M.compact lid rid x.t_u }

    (** Conjunction *)
    let meet (lx: t) (rx: t): t =
      { lx with t_u = M.meet lx.t_u rx.t_u }

    (** Forget the information on a dimension *)
    let sv_forget (id: int) (x: t): t =
      { t_e = rem_atom (Anode id) x.t_e;
        t_u = M.sv_forget id x.t_u }

    (** Export of range information *)
    (* bound of a variable *)
    let bound_variable (dim: int) (x: t): interval =
      M.bound_variable dim x.t_u

    let get_svs (x: t): IntSet.t =
      M.get_svs x.t_u

    let get_eq_class (a: int) (x: t): IntSet.t =
      if Union_find.mem (Anode a) x.t_e then
        List.fold_left
          (fun acc akey ->
            match akey with
            | Anode i -> IntSet.add i acc
            | _ -> acc
          ) IntSet.empty
          (Union_find.find_class (fst (Union_find.find (Anode a) x.t_e)) x.t_e)
      else
        IntSet.singleton a
  end: DOM_NUM_NB)
