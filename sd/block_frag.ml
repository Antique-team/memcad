(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: block_frag.ml
 **       Partitions of contiguous blocks
 ** Xavier Rival and Pascal Sotin, 2012/04/20 *)
open Data_structures
open Flags
open Lib
open Nd_sig


(** Error report *)
module Log =
  Logger.Make(struct let section = "bfrag___" and level = Log_level.DEBUG end)


(** Temporary definition for bouds
 ** Those lines will get replaced when we integrate
 ** more general forms of bounds
 **
 ** => Eventually the whold module turns into a functor *)
module Bound = Bounds
module BoundMap = MapMake( Bound )
type bound = Bound.t


(** Block partition data type, with:
 **  'a: keys, ie offsets;
 **  'b: values, ie destination nodes *)

(* A record in the map encloses an edge, and a next *)
type 'a block_entry =
    { be_elt:  'a;    (* element *)
      be_prev: bound option; (* prev key, except for the first element *)
      be_next: bound; (* next key *) }

(* A block_map contains a set of entries, bound to offsets:
 *  key->value *)
type 'a block_map = 'a block_entry BoundMap.t

(* A block fragmentation also contains the first and last values *)
type 'a block_frag =
    { bf_map:  'a block_map; (* the key->value map *)
      bf_beg:  bound; (* begin of the block: first element *)
      bf_last: bound; (* right before the end of the block: last element *)
      bf_end:  bound; (* end of the block: tail of the last element *) }
type 'a t = 'a block_frag


(** Pretty-printing *)

(* Parametric version, prints contents *)
let block_entry_2str (f: 'a -> string) (e: 'a block_entry): string =
  let sprev =
    match e.be_prev with
    | None -> "<None>"
    | Some prev -> Bound.t_2str prev in
  Printf.sprintf "[%s; %s=> ; =>%s]" (f e.be_elt) sprev
    (Bound.t_2str e.be_next)
let block_frag_2stri (ind: string) (f: 'a -> string)
    (b: 'a block_frag): string =
  let n = BoundMap.cardinal b.bf_map in
  let sep = Printf.sprintf "\n%s  " ind in
  Printf.sprintf "%smap[%d]:\n%s  %s\n%sbeg:  %s\n%slast: %s\n%send:  %s\n"
    ind n ind (BoundMap.t_2str sep (block_entry_2str f) b.bf_map)
    ind (Bound.t_2str b.bf_beg)
    ind (Bound.t_2str b.bf_last)
    ind (Bound.t_2str b.bf_end)
let block_frag_2str (f: 'a -> string) (b: 'a block_frag): string =
  block_frag_2stri "" f b

(* Short version, will not print contents *)
let block_frag_2strc: 'a block_frag -> string =
  block_frag_2str (fun _ -> ".")


(** Sanity check *)

(* The chaining property should hold:
 *  - if the first element is not in the map, the map should be empty
 *  - otherwise the map is not empty and the first element (beg) should
 *    belong to the map;
 *    . furthermore, the elements should be reached following next fields
 *      starting from the first element (beg)
 *    . all elements of the map should be reached in the traversal
 *    . the end element should be reached at the end of the traversal
 *)
let flag_verbose_frag = false
let sanity_check (ctxt: string) (b: 'a block_frag): unit =
  if flag_verbose_frag then
    Log.info "Sanity check %s:%b\n%s" ctxt (b.bf_map = BoundMap.empty)
      (block_frag_2str (fun _ -> ".") b);
  if flag_sanity_frag then
    if b.bf_map = BoundMap.empty then
      if Bound.eq b.bf_beg b.bf_end then ()
      else Log.fatal_exn "%s: sanity check; empty map; disequal bounds" ctxt
    else
      let n = BoundMap.cardinal b.bf_map in
      let rec aux (steps: int) (prev: bound option) (k: bound): bound =
        if steps >= n-1 then k
        else
          try
            let elt = BoundMap.find k b.bf_map in
            let bc =
              match prev, elt.be_prev with
              | None, None -> true
              | Some bp, Some bep -> Bound.eq bp bep
              | _, _ -> false in
            if bc then aux (steps+1) (Some k) elt.be_next
            else Log.fatal_exn "%s: sanity check; inconsistent prevs" ctxt
          with Not_found ->
            Log.fatal_exn "%s: sanity check; no next found" ctxt in
      let e = aux 0 None b.bf_beg in
      if Bound.eq e b.bf_last then
        let fend =
          try (BoundMap.find b.bf_last b.bf_map).be_next
          with Not_found ->
            Log.fatal_exn "%s: sanity check; no last found" ctxt in
        if Bound.eq fend b.bf_end then ()
        else Log.fatal_exn "%s: sanity check; last element issue" ctxt
      else
        Log.fatal_exn "%s: sanity check; does not reach end element %s"
          ctxt (Bound.t_2str e)


(** Creation *)

(* Empty block *)
let create_empty (k: bound): 'a block_frag =
  let r = { bf_map  = BoundMap.empty;
            bf_beg  = k;
            bf_last = k; (* improper, will be removed when adding an element) *)
            bf_end  = k } in
  sanity_check "create_empty,after" r;
  r  
let create_block_span (obeg: bound) (oend: bound) (v: 'a): 'a block_frag =
  let ent = { be_elt  = v;
              be_prev = None;
              be_next = oend } in
  let r = { bf_map  = BoundMap.add obeg ent BoundMap.empty;
            bf_beg  = obeg;
            bf_last = obeg;
            bf_end  = oend } in
  sanity_check "create_block_span,after" r;
  r  


(** Emptiness *)
let is_empty (b: 'a block_frag): bool =
  sanity_check "is-empty" b;
  b.bf_map = BoundMap.empty
let is_not_empty (b: 'a block_frag): bool = not (is_empty b)
let cardinal (b: 'a block_frag): int = BoundMap.cardinal b.bf_map
let map_to_list (b: 'a block_frag) = BoundMap.bindings b.bf_map
let elt (b: 'a block_entry): 'a = b.be_elt
let byte_size (b: 'a block_frag): int = 
  (Offs.to_int (Bound.to_offs b.bf_end)) - 
    (Offs.to_int (Bound.to_offs b.bf_beg))

(** Fixing prev and next fields *)
(* Fix prev field *)
let fix_prev (k: bound) (nprev: bound option) (b: 'a t): 'a t =
  try
    let elt = BoundMap.find k b.bf_map in
    { b with
      bf_map = BoundMap.add k { elt with be_prev = nprev } b.bf_map }
  with
  | Not_found -> b
(* Fix the prev field of the next element of some element *)
let fix_prev_next (k_old: bound) (k_new: bound) (b: 'a t): 'a t =
  if flag_verbose_frag then
    Log.info "fix_prev_next:\n - %s\n - %s"
      (Bound.t_2str k_old) (Bound.t_2str k_new);
  try
    let elt = BoundMap.find k_old b.bf_map in
    let b = fix_prev elt.be_next (Some k_new) b in
    { b with
      bf_map = BoundMap.add k_new elt (BoundMap.remove k_old b.bf_map) }
  with
  | Not_found -> b
(* Fix next field *)
let fix_next (ko: bound option) (nnext: bound) (b: 'a t): 'a t =
  match ko with
  | None -> (* first element: fix begin point *)
      { b with bf_beg = nnext }
  | Some k -> (* element in the middle, fix next link *)
      try
        let elt = BoundMap.find k b.bf_map in
        { b with
          bf_map = BoundMap.add k { elt with be_next = nnext } b.bf_map }
      with
      | Not_found ->
          Log.fatal_exn "fix_next: no previous element (case of 'Some')"
(* Rename the last element *)
let rename_end (newend: bound) (b: 'a t): 'a t =
  { (fix_next (Some b.bf_last) newend b) with
    bf_end = newend }


(** Functions for accessing an offset *)
(* Get the first bound *)
let first_bound (b: 'a block_frag): bound = b.bf_beg
(* Get the end bound *)
let end_bound (b: 'a block_frag): bound = b.bf_end
(* Checking for membership *)
let mem (k: bound) (b: 'a block_frag): bool = BoundMap.mem k b.bf_map
(* Find: extraction of a points-to edge *)
let extract (k: bound) (b: 'a block_frag): bound * 'a block_entry =
  k, BoundMap.find k b.bf_map
let find_addr (k: bound) (b: 'a block_frag): 'a =
  let _, ent = extract k b in ent.be_elt
(* Find using a sat function, in case straight access fails *)
let extract_addr_sat (sat: n_cons -> bool) (k: bound) (b: 'a block_frag)
    : bound * 'a block_entry =
  try extract k b
  with
  | Not_found ->
      let rec aux (k_lo: bound): bound * 'a block_entry =
        let elt = BoundMap.find k_lo b.bf_map in
        match Bound.t_order sat k_lo k with
        | Some c ->
            if c = 0 then k_lo, elt
            else if c < 0 then aux elt.be_next
            else raise Not_found
        | None -> aux elt.be_next in
      aux b.bf_beg
let find_addr_sat (sat: n_cons -> bool) (k: bound) (b: 'a block_frag): 'a =
  let _, ent = extract_addr_sat sat k b in ent.be_elt
(* Extraction of a chunk, specified by a lower and an upper bound *)
let extract_chunk_sat (sat: n_cons -> bool) (b_min: bound) (b_max: bound)
    (b: 'a block_frag): bound * 'a block_entry =
  let rec aux (k_lo: bound): bound * 'a block_entry =
    let elt = BoundMap.find k_lo b.bf_map in
    match Bound.t_order sat k_lo b_min with
    | None -> (* we keep looking forward, though it may not exist at all *)
        Log.info "extract_chunk_sat cmp failed (0):\n - %s\n - %s"
          (Bound.t_2str k_lo) (Bound.t_2str b_min);
        aux elt.be_next
    | Some c0 ->
        if c0 <= 0 then (* k_lo <= b_min *)
          match Bound.t_order sat b_max elt.be_next with
          | None -> (* we cannot guarantee the chunk is included, keep going *)
              Log.info "extract_chunk_sat cmp failed (1)";
              aux elt.be_next
          | Some c1 ->
              if c1 <= 0 then (* b_max < elt.be_next *)
                k_lo, elt
              else (* we cannot guarantee the chunk is included, keep going *)
                aux elt.be_next
        else raise Not_found in
  aux b.bf_beg
(* Find a chunk, specified by a lower and an upper bound *)
let find_chunk_sat (sat: n_cons -> bool) (b_min: bound) (b_max: bound)
    (b: 'a block_frag): 'a =
  let _, ent = extract_chunk_sat sat b_min b_max b in ent.be_elt
(* Appends an element at the beginning of a block *)
let append_head (bnd: bound) (x: 'a) (bf: 'a block_frag): 'a block_frag =
  sanity_check "append_head,before" bf;
  let elt = { be_elt  = x;
              be_prev = None;
              be_next = bf.bf_beg } in
  let nb = { bf with
             bf_beg = bnd;
             bf_map = BoundMap.add bnd elt bf.bf_map } in
  let r =
    if bf.bf_map = BoundMap.empty || Bound.eq bf.bf_last bf.bf_end then
      (* the fragmentation was empty; fix last element *)
      { nb with bf_last = bnd; }
    else (* the fragmentation was not empty; fix prev of former first element *)
      fix_prev bf.bf_beg (Some bnd) nb in
  sanity_check "append_head,after" r;
  r
(* Appends an element at the end of a block *)
let rec append_tail
    ?(nochk: bool = false) (* de-activates check that bounds coincide (join) *)
    (kbeg: bound) (kend: bound) (* begin and end bounds of the zone to add *)
    (v: 'a) (b: 'a block_frag) (* element to add and block *)
    : 'a block_frag (* block partition with additional sub-block appended *) =
  sanity_check "append_tail,before" b;
  let emp = is_empty b in
  let ent = { be_elt  = v;
              be_prev = if emp then None else Some b.bf_last;
              be_next = kend } in
  let r =
    if emp then (* Empty case *)
      if Bound.eq kbeg b.bf_beg then
        { bf_map  = BoundMap.add kbeg ent b.bf_map;
          bf_beg  = kbeg;
          bf_last = kbeg;
          bf_end  = kend; }
      else Log.fatal_exn "append_tail: empty case, bound not coinciding"
    else if Bound.eq kbeg b.bf_end then
      (* Final bounds coincide *)
      let elast =
        let l =
          try BoundMap.find b.bf_last b.bf_map
          with Not_found ->
            Log.fatal_exn "append_tail: last element not found" in
        { l with be_next = kbeg } in
      { b with
        bf_map  = BoundMap.add kbeg ent (BoundMap.add b.bf_last elast b.bf_map);
        bf_last = b.bf_end;
        bf_end  = kend; }
    else if nochk then
      (* Final bounds do not coincide,
       * but this is part of a join, so we replace the final bound with
       * an enriched bound and we restart *)
      let b_end = Bounds.merge kbeg b.bf_end in
      append_tail b_end kend v (rename_end b_end b)
    else
      match Bound.compat kbeg b.bf_end with
      | Some b_end ->
          (* Change the bound for the end of the structure, and retry *)
          append_tail b_end kend v (rename_end b_end b)
      | None -> Log.fatal_exn "append_tail: block not coinciding" in
  sanity_check "append_tail,after" r;
  r
(* Replacing a field with another one *)
let replace_sat
    (sat: n_cons -> bool)
    (k: bound) (v: 'a) (b: 'a block_frag): 'a block_frag =
  sanity_check "replace,before" b;
  let k_old, oent =
    try extract_addr_sat sat k b
    with Not_found -> Log.fatal_exn "replace: no element to replace" in
  let nmap =
    BoundMap.add k_old { oent with be_elt = v }
      (BoundMap.remove k_old b.bf_map) in
  let r = { b with bf_map = nmap } in
  sanity_check "replace,after" r;
  r

(* Splitting of a fragmentation:
 *  - removes one points-to edge;
 *  - adds two points-to edges *)
let split_sat
    (sat: n_cons -> bool)
    (klo: bound) (kmid: bound) (khi: bound)
    (vlo: 'a) (vhi: 'a) (b: 'a block_frag): 'a block_frag =
  (* we preserve the previous names for low and high bounds
   *  -> it may make sense to merge bounds at some point *)
  sanity_check "split, before" b;
  let old_klo, ent = extract_addr_sat sat klo b in
  let old_khi = ent.be_next in
  let new_khi = Bound.merge khi old_khi in
  let new_klo = Bound.merge klo old_klo in
  if flag_verbose_frag then
    Log.info "SPLIT, high:\n - arg %s\n - old %s\n - new %s"
      (Bound.t_2str khi) (Bound.t_2str old_khi) (Bound.t_2str new_khi);
  begin
    match Bound.t_order sat khi ent.be_next with
    | Some 0 -> ()
    | None -> Log.fatal_exn "none"
    | _ -> Log.fatal_exn "split: high point does not coincide %s %s"
             (Bound.t_2str khi) (Bound.t_2str ent.be_next)
  end;
  let entlo = { be_elt  = vlo;
                be_prev = ent.be_prev;
                be_next = kmid } in
  let enthi = { be_elt  = vhi;
                be_prev = Some new_klo;
                be_next = new_khi } in
  let b = fix_next ent.be_prev new_klo b in
  let b = fix_prev old_khi (Some kmid) b in
  let b = fix_prev_next old_khi new_khi b in
  let nmap =
    BoundMap.add new_klo entlo
      (BoundMap.add kmid enthi (BoundMap.remove old_klo b.bf_map)) in
  let r =
    match Bound.t_order sat klo b.bf_last with
    | Some 0 -> (* we need to update field last *)
        { b with
          bf_last = kmid;
          bf_end  = new_khi;
          bf_map  = nmap; }
    | _ ->
        { b with
          bf_map  = nmap; } in
  sanity_check "split, after" r;
  r


(** Iterators *)

(* Map function, with action on keys and on values *)
let map_bound (fkey: bound -> bound) (fval: 'a -> 'a) (b: 'a block_frag)
    : 'a block_frag =
  sanity_check "map, before" b;
  let nm =
    BoundMap.fold
      (fun k ent acc ->
        let ent0 = { be_elt  = fval ent.be_elt;
                     be_prev = Option.map fkey ent.be_prev;
                     be_next = fkey ent.be_next } in
        BoundMap.add (fkey k) ent0 acc
      ) b.bf_map BoundMap.empty in
  let r = { bf_map  = nm;
            bf_beg  = fkey b.bf_beg;
            bf_last = fkey b.bf_last;
            bf_end  = fkey b.bf_end } in
  sanity_check "map, after" r;
  r

(* Iter function (over the map structure *)
let iter_base (f: bound -> 'a -> unit) (b: 'a block_frag): unit =
  BoundMap.iter (fun b be -> f b be.be_elt) b.bf_map

(* Iter function, over the bounds (not the elements) "end" bound included *)
let iter_bound (f: bound -> unit) (b: 'a block_frag): unit =
  BoundMap.iter (fun b _ -> f b) b.bf_map;
  f b.bf_end

(* Fold over the map structure (i.e., not the list structure *)
let fold_base (f: bound -> 'a -> 'b -> 'b) (b: 'a block_frag): 'b -> 'b =
  sanity_check "fold, before" b;
  BoundMap.fold (fun k ent -> f k ent.be_elt) b.bf_map

(* Fold over the list structure, i.e., in the ascending order *)
let fold_list_base (f: bound -> 'a -> 'b -> 'b) (b: 'a block_frag): 'b -> 'b =
  let rec aux (cur_bnd: bound) (acc: 'b): 'b =
    if Bound.eq cur_bnd b.bf_end then acc
    else
      let elt =
        try BoundMap.find cur_bnd b.bf_map
        with Not_found -> Log.fatal_exn "fold_list, not found bound" in
      aux elt.be_next (f cur_bnd elt.be_elt acc) in
  aux b.bf_beg

(* Fold over the list structure, i.e., in the ascending order,
 * up to some given depth;
 * it will crash if there are not enough elements in the structure *)
let fold_list_depth (f: bound -> 'a -> 'b -> 'b)
    (dpth: int) (* depth up to which the traversal will be done *)
    (b: 'a block_frag) (x: 'b): 'b =
  let rec aux (k: int) (cur_bnd: bound) (acc: 'b): 'b =
    if k = 0 then acc
    else
      let elt =
        try BoundMap.find cur_bnd b.bf_map
        with Not_found -> Log.fatal_exn "fold_list_depth, not found bound" in
      aux (k-1) elt.be_next (f cur_bnd elt.be_elt acc) in
  aux dpth b.bf_beg x

(* Fold over the list structure, with two arguments *)
let fold_list2_bound2 (* iterated function applies to two pairs of bounds *)
    (f: bound * bound -> bound * bound -> 'a -> 'a -> 'b -> 'b)
    (b0: 'a t) (b1: 'a t) (acc: 'b): 'b =
  assert (cardinal b0 = cardinal b1);
  let rec aux (cur_bnd0: bound) (cur_bnd1: bound) (acc: 'b): 'b =
    if Bound.eq cur_bnd0 b0.bf_end then acc
    else
      let _, elt0 = extract cur_bnd0 b0
      and _, elt1 = extract cur_bnd1 b1 in
      aux elt0.be_next elt1.be_next
        (f (cur_bnd0, elt0.be_next) (cur_bnd1, elt1.be_next)
           elt0.be_elt elt1.be_elt acc) in
  aux b0.bf_beg b1.bf_beg acc
let fold_list2_bound1 (* iterated function applies to one pair of bounds *)
    (f: bound -> bound -> 'b -> 'b)
    (b0: 'a t) (b1: 'a t) (acc: 'b): 'b =
  assert (cardinal b0 = cardinal b1);
  let rec aux (cur_bnd0: bound) (cur_bnd1: bound) (acc: 'b): 'b =
    if Bound.eq cur_bnd0 b0.bf_end then f cur_bnd0 cur_bnd1 acc
    else
      let _, elt0 = extract cur_bnd0 b0
      and _, elt1 = extract cur_bnd1 b1 in
      aux elt0.be_next elt1.be_next (f cur_bnd0 cur_bnd1 acc) in
  aux b0.bf_beg b1.bf_beg acc
let fold_list2_base (* iterated function applies to one pair of bases *)
    (f: bound -> bound -> 'a -> 'a -> 'b -> 'b)
    (b0: 'a t) (b1: 'a t) (acc: 'b): 'b =
  assert (cardinal b0 = cardinal b1);
  let rec aux (cur_bnd0: bound) (cur_bnd1: bound) (acc: 'b): 'b =
    if Bound.eq cur_bnd0 b0.bf_end then acc
    else
      let _, elt0 = extract cur_bnd0 b0
      and _, elt1 = extract cur_bnd1 b1 in
      aux elt0.be_next elt1.be_next
        (f cur_bnd0 cur_bnd1 elt0.be_elt elt1.be_elt acc) in
  aux b0.bf_beg b1.bf_beg acc
    

(* Computation of reach information *)
let reach (f: IntSet.t -> 'a -> IntSet.t) (b: 'a block_frag): IntSet.t =
  let acc = Bound.t_sym_var_ids_add IntSet.empty b.bf_beg in
  let acc = Bound.t_sym_var_ids_add acc b.bf_last in
  let acc = Bound.t_sym_var_ids_add acc b.bf_end in
  fold_base
    (fun k elt acc ->
      f (Bound.t_sym_var_ids_add acc k) elt
    ) b acc


(** Second unification attempt *)
let extract_rem_first
    (b: 'a block_frag): (bound * 'a) * 'a block_frag =
  Log.info "extract_rem_first:\n%s"
    (block_frag_2stri "  " (fun _ -> ".") b);
  let elt =
    try BoundMap.find b.bf_beg b.bf_map
    with Not_found ->
      Log.fatal_exn "extract_rem_first applied to empty block_frag" in
  let beg = elt.be_next in
  sanity_check "extract_rem_first, before" b;
  let brem = { b with
               bf_beg = beg;
               bf_map = BoundMap.remove b.bf_beg b.bf_map } in
  (* fix prev element of the next entry *)
  let brem = fix_prev beg None brem in
  (* check whether the structure becomes empty *)
  let brem =
    if brem.bf_map = BoundMap.empty then
      { brem with
        bf_last = beg;
        bf_end  = beg }
    else brem in
  (* Some checks to do: last *)
  sanity_check "extract_rem_first, after" brem;
  (b.bf_beg, elt.be_elt), brem
