(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: statistics.mli
 **       Logging some statistics gathered during the analysis
 ** Xavier Rival, 2012/10/06 *)
open Data_structures
open Lib


(* statistics about *one* abstract invariant
 *  - for now, just disjuncts
 *  - possibly add info about graph sizes, num predicates... *)
type ainv_stats =
    { as_dir_disjuncts:   int; (* number of disjuncts in direct flow *)
      as_break_disjuncts: int; (* disjuncts in break flow *)}

(* statistics over a whole program *)
type prog_stats = ainv_stats list IntMap.t

(** Functions to extract and display statistics *)
(* Statistics about join and similar things *)
val print_statistics: prog_stats -> unit

(** statistics on the reduction operator *)
(* number of reduction_eager calls *)
val red_stat_eager_call: int ref
(* number of reduction_read calls *)
val red_stat_read_call: int ref
(* number of reduction_complete calls *)
val red_stat_complete_call: int ref
(* number of reduction_materialize calls *)
val red_stat_materialize_call: int ref
(* number of rigid path rule applied *)
val red_stat_num_rigid_edge_rule: int ref
(* number of C-path rule applied *)
val red_stat_num_c_path_rule: int ref
(* number of discovered equalities *)
val red_stat_num_disc_eq: int ref
(* number of discovered bottom *)
val red_stat_disc_bot_from_sp: int ref (* in sp-domain *)
val red_stat_disc_bot_aft_ens: int ref (* while ensuring *)
val reduction_mode_2str: unit -> string
val show_red_statistics: unit -> unit

(** Statistics on the garbage collection of graph structures *)
val gc_stat_full_rem: int ref (* number of nodes removed, full gc *)
val gc_stat_full_num: int ref (* number gc cycles, full gc *)
val gc_stat_incr_rem: int ref (* number of nodes removed, full gc *)
val gc_stat_incr_num: int ref (* number gc cycles, full gc *)
val show_gc_statistics: unit -> unit

