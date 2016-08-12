(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_strategies.mli
 **       functions to discover strategies for other transfer functions
 ** Xavier Rival, 2012/02/23 *)
open Data_structures
open Graph_sig
open Ind_sig

(** Extraction of inductives compatible with a points-to edge *)
val extract_compatible_inductives:
    bool -> (* whether we search for a segment (no emp case needed) *)
      pt_edge Block_frag.t -> ind StringMap.t

(** Search for possible segment directions *)
val extract_segment_directions:
    IntSet.t -> (* starting nodes *)
      Offs.OffSet.t -> (* the set of offsets that can be used in traversal *)
        graph -> (int * int) list
      
