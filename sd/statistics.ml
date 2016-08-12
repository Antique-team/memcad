(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: statistics.ml
 **       Logging some statistics gathered during the analysis
 ** Xavier Rival, 2012/08/10 *)
open Data_structures
open Flags
open Lib

module Log =
  Logger.Make(struct let section = "stats___" and level = Log_level.DEBUG end)

(* statistics about *one* abstract invariant
 *  - for now, just disjuncts
 *  - possibly add info about graph sizes, num predicates... *)
type ainv_stats =
    { as_dir_disjuncts:   int; (* number of disjuncts in direct flow *)
      as_break_disjuncts: int; (* disjuncts in break flow *)}

(* statistics over a whole program *)
type prog_stats = ainv_stats list IntMap.t

(** Functions to extract and display statistics *)
let print_statistics (s: prog_stats): unit =
  (* Exhaustive pretty-printing of disjuncts per point *)
  show_sep ();
  Log.force "Statistics; disjuncts for each point:";
  IntMap.iter
    (fun i l ->
      let n = List.fold_left (fun acc s -> acc + s.as_dir_disjuncts) 0 l in
      Log.force "  line %d \t=>\t%d [%s]" i n
        (gen_list_2str "" (fun s -> string_of_int s.as_dir_disjuncts) "," l);
    ) s;
  (* Computation of histograms and average information *)
  let n_contexts = ref 0
  and m_histo_disj_dir = ref IntMap.empty in
  let nincr n =
    let o = try IntMap.find n !m_histo_disj_dir with Not_found -> 0 in
    m_histo_disj_dir := IntMap.add n (1+o) !m_histo_disj_dir in
  IntMap.iter
    (fun i is ->
      incr n_contexts;
      List.iter
        (fun a ->
          nincr a.as_dir_disjuncts
        ) is
    ) s;
  let ntotdisj =
    IntMap.fold (fun n k acc -> acc + k * n) !m_histo_disj_dir 0 in
  let average = (float_of_int ntotdisj) /. (float_of_int !n_contexts) in
  Log.force "Disjuncts:\t\t%d\nContexts:\t\t%d\nAverage disjuncts:\t%.2f"
    ntotdisj !n_contexts average;
  Log.force "Histogram information:\n%s\n"
    (IntMap.t_2str "\n" string_of_int !m_histo_disj_dir);
  show_sep ()


(** statistics on the reduction operator *)
(* number of reduction_eager calls *)
let red_stat_eager_call: int ref = ref 0       
(* number of reduction_read calls *)
let red_stat_read_call: int ref = ref 0       
(* number of reduction_complete calls *)
let red_stat_complete_call: int ref = ref 0       
(* number of reduction_materialize calls *)
let red_stat_materialize_call: int ref = ref 0       
(* number of rigid path rule applied *)
let red_stat_num_rigid_edge_rule: int ref = ref 0
(* number of C-path rule applied *)
let red_stat_num_c_path_rule: int ref = ref 0
(* number of discovered equalities *)
let red_stat_num_disc_eq: int ref = ref 0
(* number of discovered bottom *)
let red_stat_disc_bot_from_sp: int ref = ref 0 (* in sp-domain *)
let red_stat_disc_bot_aft_ens: int ref = ref 0 (* while ensuring *)
(* Printing of the statistics *)
let reduction_mode_2str (): string = 
  match !reduction_mode_selector with
  | Rm_disabled           -> "disabled"
  | Rm_manual             -> "manual"
  | Rm_minimal            -> "minimal"
  | Rm_on_read            -> "on read"
  | Rm_on_read_and_unfold -> "on read and unfold"
  | Rm_maximal            -> "maximal"
let show_red_statistics (): unit = 
  if flag_reduction_stat then
    begin
        show_sep ();
      Log.info "Reduction statistics (%s mode):"
        (reduction_mode_2str ());
      Log.info " - eager reduction:            %d calls"
        !red_stat_eager_call;
      Log.info " - completion:                 %d calls"
        !red_stat_complete_call;
      Log.info " - read:                       %d calls"
        !red_stat_read_call;
      Log.info " - materialization:            %d calls"
        !red_stat_materialize_call;
      Log.info " - # rigid edge rule applied:  %d "
        !red_stat_num_rigid_edge_rule;
      Log.info " - # c-path rule applied:      %d "
        !red_stat_num_c_path_rule;
      Log.info " - # discovered equalities:    %d "
        !red_stat_num_disc_eq;
      Log.info " - # discovered bottoms:       %d (%d + %d)"
        (!red_stat_disc_bot_from_sp + !red_stat_disc_bot_aft_ens)
        !red_stat_disc_bot_from_sp !red_stat_disc_bot_aft_ens;
    end


(** Statistics on the garbage collection of graph structures *)
let gc_stat_full_rem: int ref = ref 0 (* number of nodes removed, full gc *)
let gc_stat_full_num: int ref = ref 0 (* number gc cycles, full gc *)
let gc_stat_incr_rem: int ref = ref 0 (* number of nodes removed, full gc *)
let gc_stat_incr_num: int ref = ref 0 (* number gc cycles, full gc *)
let show_gc_statistics ( ): unit =
  if flag_gc_stat then
    begin
      show_sep ();
      Log.info "Garbage collection statistics (gc):";
      Log.info " - full gcs:        %d cycle(s); removed %d node(s)"
        !gc_stat_full_num !gc_stat_full_rem;
      Log.info " - incremental gcs: %d cycle(s); removed %d node(s)"
        !gc_stat_incr_num !gc_stat_incr_rem;
    end
