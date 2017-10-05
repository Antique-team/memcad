(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_abs.ml
 **       experimental graph abstraction algorithm
 ** Xavier Rival, 2011/08/30 *)
open Data_structures
open Flags
open Lib

open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig

open Graph_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "g_abs___" and level = Log_level.DEBUG end)

(** Local graph abstraction routine *)
(* Note on the consistence of the product abstraction:
 * -> nodes in the abstract graph should be a subset of the original
 * -> thus, no need to perform any kind of remapping here
 * The algorithms first identifies possible weakening positions
 * (for now, using the hints), and then attempts to prove inclusion
 * using inclusion check.
 *)

(* Limitations:
 * - parameters not handled
 *)

(* Function which performs one, known, attempt at a weakening *)
let perform_one_weakening
    (i: int) (* source node *)
    (iname: string) (* inductive name *)
    (ho: hint_ug option) (* hint for the inclusion algorithm *)
    (sat: n_cons -> bool) (* constraint satisfiability check *)
    (g: graph): graph =
  let ind = Ind_utils.ind_find iname in
  assert (ind.i_ipars = 0);
  assert (ind.i_spars = 0);
  (* Creation of a graph, with only one inductive edge *)
  let gcan, ie_up =
    let gn = sv_add i Ntaddr Nnone (graph_empty g.g_inds) in
    let pargs, gn = ind_args_1_make Ntaddr ind.i_ppars gn in
    assert (ind.i_ipars = 0);
    let args = { ia_ptr = pargs ;
                 ia_int = [ ];
                 ia_set = [ ]; } in
    let ie = { ie_ind  = ind ;
               ie_args = args } in
    ind_edge_add i ie gn, ie in
  if !Flags.flag_debug_shape_abs then
    Log.force "Wa: Graph to compare (%d):\n%s" i (graph_2stri "  " gcan);
  (* Exclude the source node from the hint *)
  let hint_translator (h: hint_ug): hint_ug =
    Log.info "Hint supplied to isle: %s \\ { %d }" (hint_ug_2str h) i;
    { hug_live = Aa_sets.remove i h.hug_live } in
  let hu = Option.map hint_translator ho in
  (* Application of the inclusion check algorithm *)
  let le_res =
    let inj = Aa_maps.singleton i i in
    Graph_is_le.is_le_partial None true
      ~submem:false g hu IntSet.empty sat (fun _ -> false) gcan inj
      Aa_maps.empty in
  (* Return depending on inclusion check result *)
  match le_res with
  | Ilr_not_le ->
      (* Failure case: keep the old graph *)
      if !Flags.flag_debug_shape_abs then
        Log.info "Wa (%d,%s) fails..." i iname;
      g
  | Ilr_le_rem _ ->
      (* Should not happen, as is_le_partial was asked to search for one
       * inductive edge *)
      Log.fatal_exn "is_le_partial returned unbound result"
  | Ilr_le_ind grem -> (* Success case: full inductive edge found *)
      let gext =
        let ie = { ie_ind  = ind ;
                   ie_args = ind_args_empty } in
        ind_edge_add i ie grem in
      if !Flags.flag_debug_shape_abs then
        Log.info "Wa (%d,%s) succeeds, inductive:\n%s" i
          iname (graph_2stri "  " gext);
      gext
  | Ilr_le_seg (grem, j, ie_rem, inj) -> (* Success case: segment edge found *)
      let gext =
        (* computation of parameters at source site, from ie_up and inj *)
        let mapped_args =
          let pl =
            List.map
              (fun i ->
                try IntMap.find i inj
                with Not_found -> Log.fatal_exn "segment parameter not mapped"
              ) ie_up.ie_args.ia_ptr in
          { ia_ptr = pl ;
            ia_int = (assert (ie_up.ie_ind.i_ipars = 0); [ ]);
            ia_set = (assert (ie_up.ie_ind.i_spars = 0); [ ]);
          } in
        (* parameters at destination site, from ie_rem *)
        let seg = { se_ind   = ie_up.ie_ind ;
                    se_sargs = mapped_args ;
                    se_dargs = ie_rem.ie_args ;
                    se_dnode = j } in
        seg_edge_add i seg grem in
      if !Flags.flag_debug_shape_abs then
        Log.info "Wa (%d,%s) succeeds, segment:\n%s" i
          iname (graph_2stri "  " gext);
      gext

(* Main function: iterates over the graph to attempt weakenings *)
let graph_abs
    (ho: hint_ug option) (* hint for the inclusion algorithm *)
    (sat: n_cons -> bool) (* constraint satisfiability check *)
    (g: graph): graph =
  if !Flags.flag_debug_shape_abs then
    Log.info "\n\n[Gr,al]  start graph_abs\n%s" (graph_2stri "  " g);
  (* First phase: extract a list of candidates for weakening
   *  A candidate consists into a node and an inductive name *)
  let candidates: (int * string) list ref = ref [ ] in
  IntMap.iter
    (fun i n ->
      match n.n_attr, n.n_e with
      | _, Hind _
      | _, Hemp
      | _, Hseg _
      | Attr_none, _
      | Attr_array _, _ -> ( )
      | Attr_ind ind, Hpt _ ->
          if !Flags.flag_debug_shape_abs then
            Log.info "Hint found: %s at %d" ind i ;
          candidates := (i, ind) :: ! candidates
    ) g.g_g;
  if !Flags.flag_debug_shape_abs then
    Log.info "Wa: found %d candidates: [%s]" (List.length !candidates)
      (gen_list_2str "" (fun (i,s) -> Printf.sprintf "%d:%s" i s)
         ", " !candidates);
  (* Second phase: attempts to perform weakenings marked as candidates *)
  List.fold_left
    (fun gacc (i0, ind0) ->
      perform_one_weakening i0 ind0 ho sat gacc
    ) g !candidates
