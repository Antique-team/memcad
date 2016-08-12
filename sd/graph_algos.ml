(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_algos.ml
 **       elements used for weakening algorithms on graphs
 ** Xavier Rival, 2012/04/10 *)
open Data_structures
open Flags

open Graph_sig
open Nd_sig
open Ind_sig
open Sv_sig

open Graph_utils


(** Sided algorithms support *)

(* Display *)
let side_2str: side -> string = function
  | Lft -> "left"
  | Rgh -> "right"
(* Swap side *)
let other_side: side -> side = function
  | Lft -> Rgh
  | Rgh -> Lft
(* Side element extraction *)
let sel_side (s: side) (x, y) =
  match s with
  | Lft -> x
  | Rgh -> y
let get_sides (s: side) (x, y) =
  match s with
  | Lft -> y, x
  | Rgh -> x, y

(** Partial inclusion tests into inductive and segment edges *)

(* Construction of a graph with only one inductive edge
 * followed by inclusion checking of the side into that segment:
 *  - pointer parameters instantiable to other nodes
 *  - integer parameters instantiable to expressions *)
let is_le_ind
    ~(submem: bool) (* whether sub-memory is_le (no alloc check) *)
    (ind: ind) (* inductive definition to use for weakening *)
    (ino: graph) (* graph to weaken *)
    (iso: int) (* index of the node from which to weaken *)
    (sato: n_cons -> bool) (* constraint verification *)
    : is_le_res * ind_edge * IntSet.t =
  let g1, ieo, ino, instantiable_nodes =
    let g0 = sv_add iso Ntaddr Nnone (graph_empty ino.g_inds) in
    let ppars, ino = ind_args_1_make Ntaddr ind.i_ppars ino in
    let ie, ino = ind_edge_make ind.i_name ppars ind.i_ipars ino in
    let f_buildpars = List.fold_left (fun acc i -> IntSet.add i acc) in
    let ia_nodes = f_buildpars IntSet.empty ie.ie_args.ia_int in
    let pa_nodes = f_buildpars IntSet.empty ie.ie_args.ia_ptr in
    let g0 = IntSet.fold (fun i -> sv_add i Ntint Nnone) ia_nodes g0 in
    let g0 = IntSet.fold (fun i -> sv_add i Ntaddr Nnone) pa_nodes g0 in
    ind_edge_add iso ie g0, (* graph to use in the comparison *)
    ie,                     (* "other side" weakened inductive edge *)
    ino,                    (* "other side" graph *)
    ia_nodes                (* instantiable nodes *) in
  (* calling the weakening function *)
  let le_res =
    let inj = Aa_maps.singleton iso iso in
    Graph_is_le.is_le_partial (Some instantiable_nodes)
      false ~submem:submem ino None IntSet.empty sato g1 inj in
  le_res, ieo, instantiable_nodes

(* Construction of a graph with only one segment edge
 * followed by inclusion checking of the right side into that segment *)
let is_le_seg
    ~(submem: bool) (* whether sub-memory is_le (no alloc check) *)
    (ind: ind) (* inductive definition to use for weakening *)
    (gr: graph) (* graph to weaken *)
    (isr: int) (idr: int) (* source and destination in the right side *)
    (satr: n_cons -> bool) (* constraint verification *)
    : is_le_res * seg_edge =
  (* construction of a graph with just one segment edge *)
  let g0 =
    if isr = idr then
      sv_add isr Ntaddr Nnone (graph_empty gr.g_inds)
    else
      sv_add idr Ntaddr Nnone
        (sv_add isr Ntaddr Nnone (graph_empty gr.g_inds)) in
  let g1, ser, sinst (* set of instantiable nodes *) =
    assert (ind.i_ipars = 0); (* integer parameters not supported *)
    let lsrc, gg0 = ind_args_1_make Ntaddr ind.i_ppars g0 in
    let ldst, gg1 = ind_args_1_make Ntaddr ind.i_ppars gg0 in
    let seg =
      { se_ind   = ind ;
        se_sargs = { ia_ptr = lsrc ;
                     ia_int = [ ] } ;
        se_dargs = { ia_ptr = ldst ;
                     ia_int = [ ] } ;
        se_dnode = idr } in
    let inst = IntSet.empty in
    seg_edge_add isr seg gg1, seg, inst in
  (* calling the weakening function *)
  let le_res =
    if isr = idr then
      Ilr_le_rem (gr, IntSet.empty, IntMap.singleton isr isr, IntMap.empty)
    else
      let inj = Aa_maps.add idr idr (Aa_maps.singleton isr isr) in
      Graph_is_le.is_le_partial (Some sinst)
        false ~submem:submem gr None (IntSet.singleton idr) satr g1 inj in
    le_res, ser
