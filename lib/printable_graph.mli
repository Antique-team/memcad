(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: printable_graph.ml
 **       Graph meant to be printed out
 ** Francois Berenger, 2016/11/22 *)

open Data_structures
open Sv_sig

module Node : sig
  type kind = Plain | Ind_start | Seg_start
  type t = { id:        int;
             name:      string;
             kind:      kind;
             nb_fields: int;
             typ:       ntyp }
  val create: int -> string -> kind -> int -> ntyp -> t
  (* graphviz dot format string output *)
  val to_dot_string: t -> string
end

module Edge : sig
  type kind = Simple | Segment
  type t =
    { src_nid: int; (* source nid *)
      src_off: int; (* offset in source node *)
      dst_nid: int; (* destination nid *)
      dst_off: int; (* offset in destination node *)
      label: string;
      kind: kind }
  val create: int -> int -> int -> int -> string -> kind -> t
  (* graphviz dot format string output *)
  val to_dot_string: t -> string
end

module Graph : sig
  type t =
    { nodes: Node.t list; (* all nodes *)
      edges: Edge.t list; (* all edges *)
      title: string }
  val create: Node.t list -> Edge.t list -> string -> t
  (* graphviz dot format string output *)
  val to_dot_string: t -> string
  (* only output connected components containing any
     of the selected variables *)
  val connected_component: IntSet.t -> t -> t
  (* only output successors (direct or transitive)
     of the selected variables, plus the selected variables *)
  val successors_only: IntSet.t -> t -> t
  (* cut out leaves which are not inductive edges *)
  val cut_ordinary_leaves: t -> t
end
