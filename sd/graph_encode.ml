(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_visu.ml
 **       export graphs for visualization in the dot format for graphviz
 ** Francois Berenger and Huisong Li, started 2015/02/24 *)

(*${*) (* start injection of code for unit tests: this is necessary
          in order to bypass the fact that only a few functions are exported
          outside via the interface file but we are testing
          an internal function *)

open Data_structures
open Dom_sig
open Dom_timing
open Graph_sig
open Graph_utils
open Graph_visu
open Graph_visu_atom
open Graph_visu_common
open Ind_utils
open Ind_sig
open Sv_sig

module L = BatList
module Log =
  Logger.Make(struct let section = "g_encode" and level = Log_level.DEBUG end)

module Graph_encode: GRAPH_ENCODE = struct

  let get_uid_exn (namer: namer) (id: int): int =
    snd (namer id)

  let is_named_var (namer: namer) (id: int): bool =
    try
      let _, _ = namer id in
      true
    with Not_found -> false

  let allowed_offsets = function
    | Offset _ -> failwith "allowed_offsets: offset"
    | Baby_segment _ -> failwith "allowed_offsets: baby segment"
    | Segment (_seg_name, offsets) -> offsets

  let is_allowed_in_seg o seg =
    List.mem o (allowed_offsets seg)

  let offset = function
    | Offset o -> o
    | Segment _ -> failwith "offset: segment"
    | Baby_segment _ -> failwith "offset: baby segment"

  (* check that all steps are offsets that can be folded into the segment *)
  let can_fold (seg: step) (steps: step list): bool =
    let offsets = allowed_offsets seg in
    L.for_all
      (fun o' ->
         let o = offset o' in
         List.mem o offsets
      ) steps

  type path_after_split =
    | No_segment of step list (* only offsets *)
    | One_segment of step list * step * step list (* (offs_bef, seg, offs_aft) *)
    | Several_segments of step list * step (* (offsets, segment) *)

  (* classify steps based on the number of segments in them *)
  let split_path (steps: step list): path_after_split =
    let offsets, segments = L.partition is_offset steps in
    match segments with
    | [] -> No_segment offsets
    | [seg] -> (* one segment *)
      begin
        let i = List.index seg steps in
        let offs_before_seg, rest = L.takedrop i steps in
        let seg', offs_after_seg = L.takedrop 1 rest in
        match seg' with
        | [s] ->
          assert(s = seg);
          One_segment (offs_before_seg, seg, offs_after_seg)
        | _ -> assert(false) (* impossible *)
      end
    | _ :: _ :: _ -> (* several segments that must be equal *)
      match L.unique segments with
      | _ :: _ :: _ -> failwith "split_path: different segments"
      | [] -> assert(false) (* impossible *)
      | [seg] -> Several_segments (offsets, seg)

  let unsplit_path (before: step list) (seg: step) (after: step list)
      : step list =
    assert(is_segment seg);
    before @ (seg :: after)

  (* extend segment to its right: offsets at the right of the segment
   * are folded into the segment if they are allowed offsets of it *)
  let seg_extend_right (path: step list): step list * step * step list =
    match split_path path with
    | No_segment _ -> failwith "seg_extend_right: no segment"
    | Several_segments _ -> failwith "seg_extend_right: several segments"
    | One_segment (offs_before_seg, seg, offs_after_seg) ->
      let allowed = allowed_offsets seg in
      let _folded, rest =
        L.span (fun o -> L.mem (offset o) allowed) offs_after_seg in
      (offs_before_seg, seg, rest)

  (* extend segment to its left: offsets at the left of the segment
   * are folded into the segment if they are allowed offsets of it
   * (just a tricky version of seg_extend_right) *)
  let seg_extend_left (path: step list): step list * step * step list =
    match split_path path with
    | No_segment _ -> failwith "seg_extend_left: no segment"
    | Several_segments _ -> failwith "seg_extend_left: several segments"
    | One_segment (offs_before_seg, seg, offs_after_seg) ->
      let allowed = allowed_offsets seg in
      let _folded, rest =
        L.span (fun o -> L.mem (offset o) allowed) (L.rev offs_before_seg) in
      (L.rev rest, seg, offs_after_seg)

  let string_of_steps (steps: step list): string =
    let string_of_step (s: step): string =
      let string_of_offset o =
        Printf.sprintf "o%d" (Offs.to_int o) in
      match s with
      | Baby_segment _ -> failwith "string_of_steps: baby segment"
      | Offset o -> string_of_offset o
      | Segment (seg_name, offsets) ->
        ("seg:"
         ^ seg_name
         ^ "=("
         ^ (Lib.gen_list_2str "" string_of_offset "|" offsets)
         ^ ")*")
    in
    let buff = Buffer.create 80 in
    Buffer.add_char buff '[';
    let started = ref false in
    L.iter
      (fun s ->
         if !started then Buffer.add_string buff "; "
         else started := true;
         Buffer.add_string buff (string_of_step s)
      ) steps;
    Buffer.add_char buff ']';
    Buffer.contents buff

  (* If there is at most one segment:
   *   extend the segment in the path (if any) to the maximum
   *   by folding at its extremities or return the path as is.
   * If there are several segments:
   *   check they are equal to the same seg
   *   then check all offsets are valid offsets of seg
   *   then return seg. *)
  let rec compress_path (path: step list): step list option =
    match split_path path with
    | No_segment offsets -> Some offsets
    | One_segment (_before_seg, seg, _after_seg) ->
      let rem_before_seg, _seg, _after_seg = seg_extend_left path in
      let _before_seg, _seg, rem_after_seg = seg_extend_right path in
      Some (unsplit_path rem_before_seg seg rem_after_seg)
    | Several_segments (offsets, seg) ->
      if can_fold seg offsets then Some [seg]
      else None
  (* failwith *)
  (*   (Printf.sprintf *)
  (*      "compress_path: several segments and unfoldable offsets: %s" *)
  (*      (string_of_steps path)) *)

  (* try to extend the segment to the maximum.
   * Return (Some seg) in case it can. None in case some of the offsets at the
   * left or the right of the segment cannot be folded back into the segment *)
  let seg_extend_max (path: step list): step option =
    match split_path path with
    | No_segment offsets -> assert(false)
    | One_segment (before_seg, seg, after_seg) ->
      if can_fold seg before_seg && can_fold seg after_seg
      then Some seg
      else None
    | Several_segments (offsets, seg) ->
      if can_fold seg offsets then Some seg
      else failwith "seg_extend_max: several segments and unfoldable offsets"

  (* PairSet with specific to_string and join *)
  module PairSet = struct
    include PairSet
    let to_string iis =
      let buf = Buffer.create 80 in
      iter
        (fun (offsi, dst) ->
           let str = Printf.sprintf "(%d, %d)" offsi dst in
           Buffer.add_string buf str
        ) iis;
      Buffer.contents buf
    (* return the set that is included into the other
       or None if there is no such set *)
    let join (src: t) (dst: t): t option =
      if subset src dst then Some src
      else if subset dst src then Some dst
      else None
  end

  type encoded_graph_edges = renamed_path list

  (* compute the common prefix between ll and lr; it is returned reversed
     also, the common prefix stops at the first segment occurrence
     common_prfx_l1_l2, l1_rest, l2_rest = extract_common_prefix l1 l2 *)
  let extract_common_prefix_rev ll lr =
    let rec loop acc l1 l2 = match l1, l2 with
      | [], _ | _, [] -> (acc, l1, l2)
      | x :: xs, y :: ys ->
        if x <> y || is_segment x || is_segment y then (acc, l1, l2)
        else loop (x :: acc) xs ys
    in
    loop [] ll lr

  (* return true if (lpath <= rpath) or (rpath <= lpath) *)
  let is_included_any (lpath: step list) (rpath: step list): bool =
    (* return true if (lpath <= rpath) *)
    let rec is_included_lr (lp: step list) (rp: step list): bool =
      match lp, rp with
      | [], [] -> true (* both paths empty *)
      | [], ys
      | ys, [] -> List.for_all is_segment ys  (* only segs allowed in rest *)
      | x :: xs, y :: ys ->
        match x, y with
        | Baby_segment _, _ -> failwith "is_included_lr: baby seg on left"
        | _, Baby_segment _ -> failwith "is_included_lr: baby seg on right"
        | Segment (lname, _), Segment (rname, _) ->
          if lname = rname then is_included_lr xs ys
          else false
        | Offset lo, Offset ro ->
          if lo = ro then is_included_lr xs ys
          else false
        | Offset o, (Segment _ as seg) ->
          if is_allowed_in_seg o seg then is_included_lr xs (y :: ys)
          else false
        | (Segment _ as seg), Offset o ->
          if is_allowed_in_seg o seg then is_included_lr (x :: xs) ys
          else false in
    is_included_lr lpath rpath || is_included_lr rpath lpath

  (* join two paths
     PRECONDITIONS:
     - lp and rp must start (resp. end) at equal nodes *)
  exception Cannot_join (* raised when we detect it is impossible to join *)
  let join_paths (lhs: renamed_path) (rhs: renamed_path): renamed_path option =
    let lsrc, lpath', ldst = lhs in
    let rsrc, rpath', rdst = rhs in
    match PairSet.join lsrc rsrc, PairSet.join ldst rdst with
    | None, _ | _, None -> None (* edge extremities don't match *)
    | Some src, Some dst ->
      if lpath' = rpath' then Some (src, lpath', dst) (* 1) equal paths *)
      else
        let common, lpath, rpath = extract_common_prefix_rev lpath' rpath' in
        let loffs_before_seg, lseg', loffs_after_seg =
          match split_path lpath with
          | No_segment offsets -> (offsets, None, [])
          | One_segment (before, seg, after) -> (before, Some seg, after)
          | Several_segments (offsets, seg) ->
            if can_fold seg offsets then ([], Some seg, [])
            else failwith "join_paths: cannot compress lpath w/ several segs"
        in
        let roffs_before_seg, rseg', roffs_after_seg =
          match split_path rpath with
          | No_segment offsets -> (offsets, None, [])
          | One_segment (before, seg, after) -> (before, Some seg, after)
          | Several_segments (offsets, seg) ->
            if can_fold seg offsets then ([], Some seg, [])
            else failwith "join_paths: cannot compress rpath w/ several segs"
        in
        match lseg', rseg' with
        | None, None -> None (* not any segment *)
        | Some lseg, None ->
          assert(roffs_after_seg = []);
          if roffs_before_seg = [] then
            begin match seg_extend_max lpath with
              | None -> None
              | Some _ -> Some (src, List.rev_append common [lseg], dst)
            end
          else if can_fold lseg roffs_before_seg then
            let lpath' = unsplit_path loffs_before_seg lseg loffs_after_seg in
            (* segment added to the right *)
            Some (src, List.rev_append common lpath', dst)
          else None
        | None, Some rseg ->
          assert(loffs_after_seg = []);
          if loffs_before_seg = [] then
            begin match seg_extend_max rpath with
              | None -> None
              | Some _ -> Some (src, List.rev_append common [rseg], dst)
            end
          else if can_fold rseg loffs_before_seg then
            let rpath' = unsplit_path roffs_before_seg rseg roffs_after_seg in
            (* segment added to the left *)
            Some (src, List.rev_append common rpath', dst)
          else None
        | Some lseg, Some rseg ->
          if lseg <> rseg then None (* different segments *)
          else
            try
              let lpath' =
                unsplit_path loffs_before_seg lseg loffs_after_seg in
              let rpath' =
                unsplit_path roffs_before_seg rseg roffs_after_seg in
              let before_seg =
                if loffs_before_seg = roffs_before_seg then loffs_before_seg
                else
                  let lbs, _seg, _rest = seg_extend_left lpath' in
                  let rbs, _seg, _rest = seg_extend_left rpath' in
                  if lbs = rbs then lbs
                  else raise Cannot_join in
              let after_seg =
                if loffs_after_seg = roffs_after_seg then loffs_after_seg
                else
                  let _rest, _seg, las = seg_extend_right lpath' in
                  let _rest, _seg, ras = seg_extend_right rpath' in
                  if las = ras then las
                  else raise Cannot_join in
              let unsplit = unsplit_path before_seg lseg after_seg in
              Some (src, List.rev_append common unsplit, dst)
            with Cannot_join -> None
  (*$}*) (* end code injection for unit tests *)
  (*$inject
    let rpath steps =
    let a = PairSet.of_list [(0,0)] in
    let b = PairSet.of_list [(1,0)] in
    (a, steps, b)
    let t lsteps rsteps =
    join_paths (rpath lsteps) (rpath rsteps)
    let f x =
    Some (rpath x)
    let o12 = Offset (Offs.of_int 12);;
    let o8  = Offset (Offs.of_int  8);;
    let seg = Segment ("seg", [Offs.of_int 12; Offs.of_int 8]);;
  *)
  (*$T is_included_any
    is_included_any [o12]     [seg] = true
    is_included_any [o12;o12] [seg] = true
    is_included_any [o12]     [o8]  = false
    is_included_any []        []    = true
    is_included_any []        [seg] = true
    is_included_any [o12]     []    = false
    is_included_any [seg]     []    = true
  *)

  (* unit tests for join_paths; tests can be extracted using the qtest software *)
  (*$T
    (* t means test *) \
    t [o12;seg;o12] [ o8;seg;o12] = f [    seg;o12] (* left  diff folded into segment *)
    t [o12;seg;o12] [o12;seg; o8] = f [o12;seg    ] (* right diff folded into segment *)
    t [o12;seg;o12] [o12;seg;o12] = f [o12;seg;o12] (* some segs but no diff *)
    t [    seg;o12] [o12;seg    ] = f [    seg    ] (* delta on both sides folded *)
    t [ o8;seg    ] [ o8        ] = f [ o8;seg    ] (* seg intro detected for right member *)
    t [    seg; o8] [ o8        ] = f [    seg; o8]
    t [ o8;o12    ] [ o8;o12    ] = f [ o8;o12    ] (* no diff and no segs *)
    t [ o8;seg; o8] [   seg     ] = f [    seg    ]
    t [seg; o8;seg] [ o8        ] = f [    seg    ]
    t [ o8;seg    ] [           ] = f [    seg    ] (* needed to correct bug 01 *)
    t [    seg; o8] [           ] = f [    seg    ] (* needed to correct bug 01 *)
    t [o12; o8;seg] [o12        ] = f [o12;seg    ] (* bug 01 found by HS *)
  *)

  (* successors of node 'n' in 'g' *)
  let succs (n: int) (g: graph): IntSet.t =
    Node.successors (get_node n g)

  let succs_offs (n: int) (g: graph): (step * int) list =
    Node.successors_offs (get_node n g)

  (* as succs_offs but result is a set of int pairs *)
  let succs_offs_set (n: int) (g: graph): PairSet.t =
    let todo = Node.successors_offs (get_node n g) in
    List.fold_left
      (fun acc (step, dst) ->
         match step with
         | Offset offs ->
           let offsi = Offs.to_int offs in
           PairSet.add (offsi, dst) acc
         | Baby_segment _ | Segment (_, _) -> acc (* ignored *)
      ) PairSet.empty todo

  let string_of_renamed_path ((srcs, steps, dsts): renamed_path): string =
    Printf.sprintf "({%s}, %s, {%s})" (PairSet.to_string srcs)
      (string_of_steps steps) (PairSet.to_string dsts)

  let string_of_renamed_paths (rpaths: encoded_graph_edges): string =
    let strings = L.rev_map string_of_renamed_path rpaths in
    let sorted = L.sort String.compare strings in
    let buff = Buffer.create 80 in
    L.iter
      (fun s ->
         Buffer.add_string buff s;
         Buffer.add_string buff "\n"
      ) sorted;
    Buffer.contents buff

  type path = int * step list * int

  let edges_of_graph (g: graph) (all_nodes: IntSet.t): path list =
    IntSet.fold
      (fun src_node acc1 ->
         let nexts = succs_offs src_node g in
         L.fold_left
           (fun acc2 (offset, dst_node) ->
              ((src_node, [offset], dst_node) :: acc2)
           ) acc1 nexts
      ) all_nodes []

  (* WARNING complexity = O(n); change this one day if the method is adopted *)
  let delete_node (nid: int) (edges: path list): path list =
    let node_is_dst, node_is_src, rest =
      L.fold_left
        (fun ((acc1, acc2, acc3) as acc) ((src_node, offsets, dst_node) as x) ->
           if nid = src_node then (* node is src *)
             if nid = dst_node then
               acc (* node is both, just skip it *)
             else
               (acc1, x :: acc2, acc3)
           else if nid = dst_node then (* node is dst *)
             (x :: acc1, acc2, acc3)
           else
             (acc1, acc2, x :: acc3) (* node is neither *)
        ) ([], [], []) edges in
    (* restore connectivity and update offset paths *)
    L.fold_left
      (fun acc1 (src_node, src_offs, _nid) ->
         L.fold_left
           (fun acc2 (_nid, dst_offs, dst_node) ->
              (src_node, src_offs @ dst_offs, dst_node) :: acc2
           ) acc1 node_is_src
      ) rest node_is_dst

  (* gather renamings for variable content nodes:
   * each vc_node will be renamed after all the named variable nodes
   * which are its direct predecessors in 'g' *)
  let retrieve_renaming_data (namer: namer) (g: graph)
      (vc_nodes: IntSet.t) (nv_nodes: IntSet.t): PairSet.t IntMap.t =
    let init =
      IntSet.fold
        (fun vc_id acc -> IntMap.add vc_id PairSet.empty acc )
        vc_nodes IntMap.empty in
    IntSet.fold
      (fun nv_id acc1 ->
         let all_succs_offs = succs_offs_set nv_id g in
         let vc_succs_only =
           PairSet.filter
             (fun (_offsi, nid) -> IntSet.mem nid vc_nodes)
             all_succs_offs in
         let nv_uid = get_uid_exn namer nv_id in
         PairSet.fold
           (fun (offsi, vc_id) acc2 ->
              let curr = IntMap.find vc_id acc2 in
              IntMap.add vc_id (PairSet.add (offsi, nv_uid) curr) acc2
           ) vc_succs_only acc1
      ) nv_nodes init

  type encoded_graph = encoded_graph_edges * PairSetSet.t * int

  (* keep all paths if they are of same length *)
  (* if not, keep only the shortest *)
  let shortest_path_filter paths =
    let path_len (_, path, _) =
      List.length path
    in
    let rec find_shortest_path = function
      | [] -> []
      | [x] -> [x]
      | x :: y :: zs ->
        if path_len x <= path_len y then
          find_shortest_path (x :: zs)
        else
          find_shortest_path (y :: zs)
    in
    match paths with
    | [] -> []
    | [x] -> [x]
    | x :: y :: zs ->
      let len = path_len x in
      if List.for_all (fun z -> path_len z = len) paths then
        paths (* all have same length *)
      else (* there is a shorter one *)
        find_shortest_path paths

  (* encoding used to predict if the join of two graphs should work:
   * only paths between variables' content are kept; they are also
   * "contracted", i.e. following several times the same field/offset of a struct
   * is encoded as following it only once.
   * Algorithm was written on paper by Huisong on the 31/07/2015 *)
  let encode (disj_num: int) (namer: namer) (g: graph): encoded_graph =
    let all_nodes = get_all_nodes g in
    let named_var_nodes = IntSet.filter (is_named_var namer) all_nodes in
    let var_content_nodes =
      IntSet.fold (fun elt acc ->
          IntSet.union acc (succs elt g)
        ) named_var_nodes IntSet.empty in
    let only_nv_nodes = IntSet.diff named_var_nodes var_content_nodes in
    let renamer =
      retrieve_renaming_data namer g var_content_nodes named_var_nodes in
    let named_nodes =
      IntMap.fold (fun nid name acc -> PairSetSet.add name acc)
        renamer PairSetSet.empty in
    let rename nid = IntMap.find nid renamer (* vc_node *) in
    let to_delete_nodes =
      IntSet.diff (IntSet.diff all_nodes named_var_nodes) var_content_nodes in
    (* graph encoding: remove all nodes to delete and create paths *)
    let init = edges_of_graph g all_nodes in
    let paths =
      IntSet.fold (fun elt acc -> delete_node elt acc) to_delete_nodes init in
    (* contract offset lists, rename vc_nodes and
       remove edges starting by a only nv_node *)
    let already_seen = Hashtbl.create 11 in
    let rm_dups x acc =
      if Hashtbl.mem already_seen x then
        acc
      else
        begin
          Hashtbl.add already_seen x ();
          x :: acc
        end in
    let unsorted =
      L.fold_left
        (fun acc (src, offs, dst) ->
           if IntSet.mem src only_nv_nodes then acc
           else
             let src' = rename src in
             let dst' = rename dst in
             if src' = dst' then
               acc (* path to self is not kept: only paths between distinct
                    * variables are informative *)
             else
               rm_dups (src', offs, dst') acc
        ) [] paths in
    let shortest_paths_only =
      let same_src_dst =
        BatList.group (fun (src0, _, dst0) (src1, _, dst1) ->
            let cmp = PairSet.compare src0 src1 in
            if cmp = 0 then
              PairSet.compare dst0 dst1
            else
              cmp
          ) unsorted
      in
      List.flatten (List.map shortest_path_filter same_src_dst) in
    (* we use string ordering to order paths *)
    let to_sort =
      L.map (fun p -> (string_of_renamed_path p, p)) shortest_paths_only in
    let sorted =
      L.sort (fun (str1, _p1) (str2, _p2) -> String.compare str1 str2) to_sort in
    (L.map snd sorted, named_nodes, disj_num)

  (* export an encoded shape graph to graphviz' dot format *)
  let encoded_graph_to_dot
      ((edges, nodes, _disj): encoded_graph) (out: out_channel): unit =
    let node_labels = PairSetSet.node_labels nodes in
    let _, node_label_to_index =
      List.fold (fun (i, acc) x ->
          let res = StringMap.add x i acc in
          (i + 1, res)
        ) (0, StringMap.empty) node_labels
    in
    Printf.fprintf out "digraph g {\n\
                    graph [ rankdir = \"LR\" ];\n";
    (* output nodes *)
    StringMap.iter (fun label i ->
        Printf.fprintf out "\"%d\" [label=\"%s\" shape=\"record\"];\n" i label
      ) node_label_to_index;
    (* output edges *)
    List.iter (fun (src, path, dst) ->
        let src_lbl = PairSet.node_label src in
        let dst_lbl = PairSet.node_label dst in
        let src_i = StringMap.find src_lbl node_label_to_index in
        let dst_i = StringMap.find dst_lbl node_label_to_index in
        Printf.fprintf out
          "\"%d\" -> \"%d\" [label=\"%s\"];\n" src_i dst_i (string_of_steps path)
      ) edges;
    Printf.fprintf out "}\n"

  let pp_encoded_graph
      (disj: int)
      (vars: string list)
      (g: graph)
      (namer: namer)
      (enc_dot_fn: string)
      (out: out_channel): unit =
    let root_vars = StringSet.of_list vars in
    let nodes_to_keep = successors_only root_vars g namer in
    let g' = filter_nodes nodes_to_keep g in
    let (enc_paths, enc_nodes, disj_num) as encoded = encode disj namer g' in
    Lib.with_out_file enc_dot_fn (encoded_graph_to_dot encoded);
    Printf.fprintf out "%s" (string_of_renamed_paths enc_paths)

  (** partition algorithm used for selection widening for now,
   ** need to be improve later *)

  (* compare a step list: sl can be joined with sr *)
  let can_widen_offs_path (sl: step list) (sr: step list): bool =
    (* left become empty *)
    match sl, sr with
    | [Offset offl], [Offset offr] ->
      offl = offr
    | [Offset offl], (Offset offr)::tr ->
      offl = offr
    | (Offset offl)::(Offset offl1)::tl, (Offset offr)::(Offset offr1)::tr ->
      offl = offr && offl1 = offr1
    |  (Offset offl)::tl, (Segment (_, offs))::tr ->
      List.mem offl offs
    |  (Segment (_, offs))::tl, (Offset offr)::tr ->
      List.mem offr offs
    | (Segment (indl, _))::sle, (Segment (indr, _))::sre ->
      indl = indr
    | _ -> false
    (* | [], [] -> true *)
    (* | [], [Segment (_, _)] -> true *)
    (* | [], [Offset offs] -> true *)
    (* (\* left has one element *\) *)
    (* | (Offset offl)::sle, (Offset offr)::sre-> *)
    (*   offl = offr && can_widen_offs_path sle sre *)
    (* | (Offset offl)::sle, (Segment (_, offs))::sre -> *)
    (*   List.mem offl offs && can_widen_offs_path sle sr *)
    (* | (Offset offl)::sle, _ -> false *)
    (* (\* left has one segment *\) *)
    (* | (Segment (indl, _))::sle, (Segment (indr, _))::sre -> *)
    (*   indl = indr && can_widen_offs_path sle sr *)
    (* | (Segment (indl, _))::sle, _ -> false *)
    (* | _, _ -> false *)

  (* compare two paths, used for group disjuntions in widening *)
  let can_widen_path (sl: renamed_path) (sr: renamed_path): bool =
    let bl, pl, el = sl in
    let br, pr, er = sr in
    (PairSet.subset bl br || PairSet.subset br bl) &&
    (PairSet.subset el er || PairSet.subset er el) &&
    (can_widen_offs_path pl pr || can_widen_offs_path pr pl)

  (** for checking right graph is an abstraction of left graph,
   ** used in joining partition now *)

  (* check path sr is an abstraction of path sl *)
  let rec is_le_path (sl: step list) (sr: step list): bool =
    (sl = sr) ||
    begin
      (* look two steps one time *)
      match sl, sr with
      (* left become empty *)
      | [], [] -> true
      | [], [Segment (_, _)] -> true
      | [], [Offset offs] -> false
      (* left has one element *)
      | [Offset offl], (Offset offr)::sre ->
        offl = offr && is_le_path [] sre
      | [Offset offl], (Segment (_, offs))::sre ->
        List.mem offl offs && is_le_path [] sre
      (* left has one segment *)
      | [Segment (indl, _)], (Segment (indr, _))::sre ->
        indl = indr && is_le_path [] sre
      (* look forward one more element *)
      | (Segment (indl, _))::Offset offl::sle,
        (Segment (indr, _))::Offset offr::sre ->
        indl = indr && offl = offr && is_le_path sle sre
      (* do not look forward *)
      | (Offset offl)::sle, (Offset offr)::sre->
        offl = offr && is_le_path sle sre
      | (Offset offl)::sle, (Segment (_, offs))::sre ->
        List.mem offl offs && is_le_path sle sr
      | (Segment (indl, _))::sle, (Segment (indr, _))::sre ->
        indl = indr && is_le_path sle sre
      (* otheres *)
      | _, _ -> false
    end

  (* is edge sr an abstraction of edge sl *)
  let is_le_edge (sl: renamed_path) (sr: renamed_path): bool =
    let bl, pl, el = sl in
    let br, pr, er = sr in
    PairSet.equal bl br && PairSet.equal el er && is_le_path pl pr

  (* first path: checking nodes
   * all the single nodes (nodes not in edges) in right is included in left *)
  let is_le_nodes
      ((left, left_name, _): encoded_graph)
      ((right, right_name, _): encoded_graph): bool =
    let nodes_in_graph =
      List.fold_left
        (fun acc (ps, _, pd) ->
           PairSetSet.add ps (PairSetSet.add pd acc)
        ) PairSetSet.empty right in
    let single_nodes = PairSetSet.diff right_name nodes_in_graph in
    PairSetSet.subset single_nodes left_name

  (* second path: checking segment in right graph, which abstract empty *
   * in left graph  *)
  let is_segment_empty
      ((left, left_name, _): encoded_graph)
      ((right, _,        _): encoded_graph): renamed_path list =
    (* find segment which abstracts empty and remove it from graph*)
    let rename_info, right_left =
      List.fold_left
        (fun (acc,right_left) (ps, pp, pd) ->
           let is_segment =
             match pp with
             | [(Segment (indl, _))] -> true
             | _ -> false in
           if is_segment then
             begin
               let union_node = PairSet.union ps pd in
               if PairSetSet.mem union_node left_name then
                 let acc = PairSetMap.add ps union_node acc in
                 PairSetMap.add pd union_node acc, right_left
               else acc, ((ps, pp, pd)::right_left)
             end
           else acc, ((ps, pp, pd)::right_left)
        ) (PairSetMap.empty, []) right in
    (* rename graph *)
    List.fold_left
      (fun acc  (ps, pp, pd) ->
         let ps =
           if PairSetMap.mem ps rename_info then
             PairSetMap.find ps rename_info
           else ps in
         let pd =
           if PairSetMap.mem pd rename_info then
             PairSetMap.find pd rename_info
           else pd in
         (ps, pp, pd) :: acc
      ) [] right_left

  (* third path: check edges in right graph abstract edges in left graph *)
  let is_le_edges (left: encoded_graph_edges) (right: encoded_graph_edges):
    bool =
    List.fold_left
      (fun acc edge ->
         acc && List.exists (fun ele -> is_le_edge ele edge) left
      ) true right

  (* check right graph is abstracting left graph *)
  let is_le (left: encoded_graph) (right: encoded_graph): bool =
    if is_le_nodes left right then
      let right' = is_segment_empty left right in
      is_le_edges (fst3 left) right'
    else false

  (** more general algorithm for join partition and join of encoded graphs   *)

  (* node in paths *)
  let nodes_in_paths (g: renamed_path list): PairSetSet.t =
    List.fold_left
      (fun acc (ps, _, pd) ->
         PairSetSet.add ps (PairSetSet.add pd acc)
      ) PairSetSet.empty g

  (* compute same nodes *)
  let same_nodes (ln: PairSetSet.t) (rn: PairSetSet.t): PairSetSet.t =
    PairSetSet.inter ln rn

  (* join empty-seg, find the nodes in left, which corresponding to segment
   * in the right side *)
  let emp_seg (left_name: PairSetSet.t) (right: renamed_path list):
    (renamed_path list *  PairSetSet.t) option
    * renamed_path list * PairSetSet.t =
    let outp, outn,  right_left, lname =
      List.fold_left
        (fun (outp, outn, right_left, lname) (ps, pp, pd) ->
           let pp_com = compress_path pp in
           let is_segment =
             match pp_com with
             | Some [(Segment (indl, _))] -> true
             | _ -> false in
           if is_segment then
             begin
               let union_node = PairSet.union ps pd in
               if PairSetSet.mem union_node left_name then
                 (ps, (BatOption.get pp_com), pd) :: outp,
                 PairSetSet.add ps (PairSetSet.add pd outn),
                 right_left, PairSetSet.add union_node lname
               else outp, outn, ((ps, pp, pd)::right_left), lname
             end
           else outp, outn, ((ps, pp, pd)::right_left), lname
        ) ([],  PairSetSet.empty, [], PairSetSet.empty) right in
    Some (outp, outn), right_left, (PairSetSet.diff left_name lname)

  (* joining edges in right graph and left graph  *)
  let join_edges (left: renamed_path list) (right: renamed_path list)
    : renamed_path list option =
    try
      (* for paths in left, try to find the corresponding path in right,
       * and join them *)
      let left, right, out =
        List.fold_left
          (fun (left, right, out) edge ->
             try
               let psl, ppl, pdl = edge in
               let psr, ppr, pdr =
                 List.find
                   (fun (psr, ppr, pdr) ->
                      (PairSet.subset psl psr || PairSet.subset psr psl) &&
                      (PairSet.subset pdl pdr || PairSet.subset pdr pdl)
                   ) right in
               (* join path *)
               let pso, ppo, pdo =
                 BatOption.get (join_paths edge (psr, ppr, pdr)) in
               (* remove the edge from right graph *)
               let right =
                 List.filter
                   (fun (s, p, d) ->
                      not (PairSet.equal psr s
                           && ppr = p
                           && PairSet.equal pdr d)
                   ) right in
               left, right, (pso, ppo, pdo)::out
             with
             | Not_found -> edge :: left, right, out
          ) ([], right, []) left in
      match left, right with
      | [], _ | _, [] -> Some out
      | _ -> None
    with
    | Invalid_argument _ -> None

  let fst3 (x, _, _) = x

  (* check whether a join will loss precision *)
  let test_precision_loss (ag: abs_graph): bool =
    let rec check = function
      | [] -> false
      | (sc, ph, dt) :: rest ->
        let precision_loss =
          List.exists (fun (sc1, ph1, dt1) ->
              (PairSet.equal sc sc1) &&
              (not (PairSet.equal dt dt1)) &&
              (is_included_any ph ph1)
            ) rest
        in
        if precision_loss then
          true
        else
          check rest
    in
    check (fst3 ag)

  (* canonicalization joining  *)
  let canol_join
      ((left,  left_name , l_disj): renamed_path list * PairSetSet.t * int)
      ((right, right_name, r_disj): renamed_path list * PairSetSet.t * int):
    (renamed_path list * PairSetSet.t * int) option  =
    let cano paths =
      List.map (fun (s, p, d) ->
          let p =
            match p with
            | h::tl ->
              let tl_com = compress_path tl in
              (
                match tl_com with
                | Some seg -> h::seg
                | None -> h::tl
              )
            | _ -> p in
          (s, p, d)
        ) paths in
    let left, right =cano left, cano right in
    if 
      (PairSetSet.equal left_name right_name) &&
      List.for_all (fun p ->
          List.mem p left
        ) right
      && 
      List.for_all (fun p ->
          List.mem p right
        ) left then
      Some (left, left_name, -1)
    else
      None


  (* joing the right graph with the left graph, return the joining result *
   * if cannot join, then return None *)
  let join
      ((left,  left_name , l_disj): encoded_graph)
      ((right, right_name, r_disj): encoded_graph): encoded_graph option =
    if !Flags.widen_can then
      canol_join (left,  left_name , l_disj) (right, right_name, r_disj)
    else
    (* join the common nodes in both side *)
    let out_nodes = same_nodes left_name right_name in
    (* collect the other nodes in left side and right side *)
    let lnodes_left = PairSetSet.diff left_name out_nodes  in
    let rnodes_left = PairSetSet.diff right_name out_nodes in
    try
      (* deal with left empty, right segment *)
      let out, right, lnodes_left = emp_seg lnodes_left right in
      let paths_out, nodes = BatOption.get out in
      (* out_graph and out_nodes*)
      let out_graph = paths_out in
      let out_nodes = PairSetSet.union out_nodes nodes in
      (* deal with right empty, left segment *)
      let out, left, rnodes_left = emp_seg rnodes_left left in
      let paths_out, nodes = BatOption.get out in
      let out_graph, out_nodes =
        paths_out @ out_graph, PairSetSet.union out_nodes nodes in
      (* join the other edges *)
      let paths_out =  BatOption.get (join_edges left right) in
      let out_graph = paths_out @ out_graph in
      (* join with nodes in graphs *)
      let out_nodes =  PairSetSet.union (nodes_in_paths out_graph) out_nodes in
      let rnodes_left = PairSetSet.diff rnodes_left out_nodes in
      let lnodes_left = PairSetSet.diff lnodes_left out_nodes in
      let disj_num = (-1) in (* ignored *)
      if PairSetSet.is_empty rnodes_left && PairSetSet.is_empty lnodes_left
         && not (test_precision_loss (out_graph, out_nodes, disj_num)) then
        begin
          if not !Flags.very_silent_mode then
            Log.info "out_join:%s\n" (string_of_renamed_paths out_graph);
          Some (out_graph, out_nodes, disj_num)
        end
      else None
    with
    | Invalid_argument _ -> None

  (* reduce abs_graph to paths with segment inside only *)
  let reduce_to_seg ((g, n, disj_num): abs_graph): abs_graph =
    let paths =
      List.filter
        (fun (_, p, _) ->
           List.exists
             (fun st ->
                match st with
                | Segment _ -> true
                | _ -> false
             ) p
        ) g in
    let nodes =
      List.fold_left (fun acc (sc, _, dt ) ->
          PairSetSet.add sc (PairSetSet.add dt acc)
        ) PairSetSet.empty paths in
    (paths, nodes, disj_num)

  (* reduce a graph accoding to the joining result*)
  let reduce_input
      ((g_i, n_i, disj_i): abs_graph)
      ((g_o, n_o, disj_o): abs_graph)
    : abs_graph =
    let g_i =
      List.filter
        (fun (sc, _, dt) ->
           (PairSetSet.mem sc n_o) &&  (PairSetSet.mem dt n_o)
        ) g_i in
    (g_i, n_i, disj_i)


(* canonicalization widening  *)
  let canol_widen
      ((left,  left_name , l_disj): renamed_path list * PairSetSet.t * int)
      ((right, right_name, r_disj): renamed_path list * PairSetSet.t * int): bool  =
    let cano paths =
      List.map (fun (s, p, d) ->
          let p =
            match p with
            | h::tl ->
              [h]
          | _ -> p in
          (s, p, d)
        ) paths in
    let left, right =cano left, cano right in
    (PairSetSet.equal left_name right_name) &&
    List.for_all (fun p ->
        List.mem p left
      ) right
    && 
    List.for_all (fun p ->
        List.mem p right
      ) left

  (* compare the two graphs, if the left graph can be widen with the right
   * graph *)
  let can_widen
      ((left , left_name , left_disj ): encoded_graph)
      ((right, right_name, right_disj): encoded_graph): bool =
    if !Flags.widen_can then
      canol_widen (left,  left_name , left_disj) (right, right_name, right_disj)
    else
    (* join the common nodes in both side *)
    let out_nodes = same_nodes left_name right_name in
    (* collect the other nodes in left side and right side *)
    let lnodes_left = PairSetSet.diff left_name out_nodes  in
    let rnodes_left = PairSetSet.diff right_name out_nodes in
    try
      (* deal with left empty, right segment *)
      let out, right, lnodes_left = emp_seg lnodes_left right in
      (* (\* nodes in paths *\) *)
      let res_re, _ =
        List.fold_left
          (fun (res, nodes) left_path ->
             let ps, pp, pd = left_path in
             if PairSetSet.mem (PairSet.union ps pd) left_name then
               res, PairSetSet.add ps (PairSetSet.add pd nodes)
             else
               try
                 let rps, rpp, rpd = List.find (fun right_path ->
                     left_path = right_path 
                     || can_widen_path left_path right_path
                   ) left in
                 let ops, opd = PairSet.inter ps rps, PairSet.inter pd rpd in
                 res,  PairSetSet.add ops (PairSetSet.add opd nodes)
               with Not_found -> false, nodes
          ) (true, PairSetSet.empty) right in
      let res =
        if res_re then
          PairSetSet.for_all
            (fun ele ->
               (PairSetSet.exists
                  (fun lele ->
                     PairSet.subset ele lele
                  ) left_name
               ) ||
               (List.exists
                  (fun (ps, pp, pd) ->
                     PairSet.equal ele (PairSet.union ps pd) 
                  ) 
                  left
               )
            ) rnodes_left
        else false
      in
      if not !Flags.very_silent_mode then
        begin
          Pr.printf "left_widen(D=%d):%s\n"   left_disj (string_of_renamed_paths left);
          Pr.printf "right_widen(D=%d):%s\n" right_disj (string_of_renamed_paths right);
          Pr.printf "res:%b;\n" res;
        end;
      res
    with
    | Invalid_argument _ -> false

  let to_string (ag: abs_graph_arg option): string =
    match ag with
    | None -> "None"
    | Some absg ->
        List.fold_left
          (fun acc ele ->
            let sc_str = Graph_utils.onode_2str ele.sc in
            let dt_str = Graph_utils.onode_2str ele.dt in
            let pth_str = string_of_steps ele.pth in
            Printf.sprintf "{%s, %s, %s}\n %s" sc_str pth_str dt_str acc
          ) "\n" absg

end

module Graph_encode_timing =
  functor (D: GRAPH_ENCODE) ->
    (struct
      module T = Timer.Timer_Mod( struct let name = "Graph_encode" end )
      type encoded_graph_edges = D.encoded_graph_edges
      type encoded_graph = D.encoded_graph
      let can_widen = T.app2 "can_widen" D.can_widen
      let encode = T.app3 "encode" D.encode
      let join = T.app2 "join" D.join
      let pp_encoded_graph = T.app6 "pp_encoded_graph" D.pp_encoded_graph
      let reduce_to_seg = T.app1 "reduce_to_seg" D.reduce_to_seg
      let string_of_renamed_paths =
        T.app1 "string_of_renamed_paths" D.string_of_renamed_paths
      let to_string = T.app1 "to_string" D.to_string
    end: GRAPH_ENCODE)
