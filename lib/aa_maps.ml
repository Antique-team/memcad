(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: aa_maps.ml
 **       Arne Anderson implementation for polymorphic maps
 ** Xavier Rival, 2012/11/14 *)

module Log =
  Logger.Make(struct let section = "aamaps__" and level = Log_level.DEBUG end)

(** AA tree invariants:
 ** - root is black;
 ** - left is black;
 ** - if parent is red, both children are black
 ** - black height (number of black nodes on a path) is constant
 **   and is called the level of a node (int constant bound on it
 **   = Red node means that the level is the same as the parent
 **
 ** This implementation largely follows Wikipedia's page on AA trees
 **)
type ('a, 'b) t =
  | Leaf
  | Node of ('a, 'b) t * 'a * 'b * int * ('a, 'b) t

(** Level *)
let level: ('a, 'b) t -> int = function
  | Leaf -> 0
  | Node (_, _, _, h, _) -> h

(** Sanity check *)
let do_sanity_check = false
let sanity_check (msg: string) (x: ('a, 'b) t): bool =
  let rec aux must_eq bh x =
    match x with
    | Leaf -> bh = 0 (* leaves have level 0 *)
    | Node (l, k, e, h, r) ->
        if must_eq then (* node must be black *)
          (* the level *must* be equal to bh *)
          if h != bh then failwith "h is wrong"
          else aux true (h-1) l && aux false h r
        else if h = bh then (* node is red *)
          aux true (h-1) l && aux true (h-1) r
        else if h = bh - 1 then (* node is black *)
          aux true (h-1) l && aux false h r
        else failwith "incorrect h" in
  try Log.info "<%s> structural invariant ok" msg;
    aux true (level x) x
  with
  | e ->
      Log.info "<%s> structural invariant violated: %s"
        msg (Printexc.to_string e);
      false

(** Rebalancing support *)
(* Right rotation, fixes the case of a left, red child
 * also called "skew" *)
let rotate_right (t: ('a, 'b) t): ('a, 'b) t =
  match t with
  | Node (Node (t0, k1, e1, h1, t2), k3, e3, h3, t4) ->
      if h1 = h3 then
        Node (t0, k1, e1, h1, Node (t2, k3, e3, h3, t4))
      else t
  | _ -> t
(* Left rotation, fixes the case of right, red child of a red node
 * also called "split" *)
let rotate_left (t: ('a, 'b) t): ('a, 'b) t =
  match t with
  | Node (t0, k1, e1, h1, Node (t2, k3, e3, h3, t4)) ->
      if h1 = h3 && h3 = level t4 then
        Node (Node (t0, k1, e1, h1, t2), k3, e3, h3 + 1, t4)
      else t
  | _ -> t
(* Rebalancing of a node *)
let node_rebal (t: ('a, 'b) t): ('a, 'b) t =
  rotate_left (rotate_right t)
(* Decrease level when applicable *)
let decrease_level (t: ('a, 'b) t): ('a, 'b) t =
  match t with
  | Leaf -> t
  | Node (l, k, e, h, r) ->
      let should_be = min (level l) (level r + 1) in
      if should_be < h then
        let r =
          match r with
          | Leaf -> r
          | Node (rl, rk, re, rh, rr) ->
              if should_be < rh then Node (rl, rk, re, should_be, rr)
              else r in
        Node (l, k, e, should_be, r)
      else t

(** Utility substitution *)
let rec get_mini (t: ('a, 'b) t): 'a * 'b =
  match t with
  | Leaf -> failwith "get_replace_maxi"
  | Node (l, k, e, h, r) ->
      if l = Leaf then k, e
      else get_mini l
let rec get_maxi (t: ('a, 'b) t): 'a * 'b =
  match t with
  | Leaf -> failwith "get_replace_maxi"
  | Node (l, k, e, h, r) ->
      if r = Leaf then k, e
      else get_maxi r
let op_right (f: ('a,'b) t -> ('a,'b) t) t =
  match t with
  | Leaf -> Leaf
  | Node (l, k, e, h, r) -> Node (l, k, e, h, f r)
let op_right_right  (f: ('a,'b) t -> ('a,'b) t) =
  op_right (op_right f)

(** Basic functions (accesses, add, remove) *)
(* Empty element *)
let empty: ('a, 'b) t = Leaf
(* Emptiness test *)
let is_empty = function
  | Leaf -> true
  | Node _ -> false
(* Membership test *)
let mem (k0: 'a): ('a, 'b) t -> bool =
  let rec aux (t: ('a, 'b) t): bool =
    match t with
    | Leaf -> false
    | Node (l, k, _, _, r) ->
        let c = compare k0 k in
        if c < 0 then aux l
        else if c > 0 then aux r
        else true in
  aux
(* Finding an element *)
let find (k0: 'a): ('a, 'b) t -> 'b =
  let rec aux t =
    match t with
    | Leaf -> raise Not_found
    | Node (l, k, e, _, r) ->
        let c = compare k0 k in
        if c < 0 then aux l
        else if c > 0 then aux r
        else e in
  aux
(* Adding an element *)
let add (k0: 'a) (x: 'b): ('a, 'b) t -> ('a, 'b) t =
  let rec aux t =
    match t with
    | Leaf -> Node (Leaf, k0, x, 1, Leaf)
    | Node (l, k, e, h, r) ->
        let comp = compare k0 k in
        if comp = 0 then Node (l, k, x, h, r)
        else
          let nt =
            if comp < 0 then Node (aux l, k, e, h, r)
            else Node (l, k, e, h, aux r) in
          node_rebal nt in
  fun t ->
    if do_sanity_check then ignore (sanity_check "add,before" t);
    let r = aux t in
    if do_sanity_check then ignore (sanity_check "add,after" r);
    r
(* Removing an element *)
let rec remove (k0: 'a) (t: ('a, 'b) t): ('a, 'b) t =
  if do_sanity_check then ignore (sanity_check "rem,before" t);
  (* remove *)
  let r =
    match t with
    | Leaf -> t
    | Node (l, k, e, h, r) ->
        let comp = compare k0 k in
        if comp = 0 then
          if l = Leaf then
            if r = Leaf then
              Leaf
            else (* remove successor *)
              let ka, ea = get_mini r in
              Node (l, ka, ea, h, remove ka r)
          else (* remove predecessor *)
            let ka, ea = get_maxi l in
            Node (remove ka l, ka, ea, h, r)
        else if comp < 0 then Node (remove k0 l, k, e, h, r)
        else Node (l, k, e, h, remove k0 r) in
  (* rebalance *)
  let r = decrease_level r in
  let r = rotate_right r in
  let r = op_right rotate_right r in
  let r = op_right_right rotate_right r in
  let r = rotate_left r in
  let r = op_right rotate_left r in
  if do_sanity_check then ignore (sanity_check "rem,after" r);
  r
(* Singleton map *)
let singleton (k: 'a) (x: 'b): ('a, 'b) t = add k x empty

(** Iterators *)
let iter (f: 'a -> 'b -> unit): ('a, 'b) t -> unit =
  let rec aux t =
    match t with
    | Leaf -> ( )
    | Node (l, k, e, _, r) ->
        aux l;
        f k e;
        aux r in
  aux
let map (f: 'b -> 'c): ('a, 'b) t -> ('a, 'c) t =
  let rec aux t =
    match t with
    | Leaf -> Leaf
    | Node (l, k, e, c, r) -> Node (aux l, k, f e, c, aux r) in
  aux
let rec fold_left (f: 'a -> 'b -> 'c -> 'c) (t: ('a, 'b) t) (accu: 'c): 'c =
  match t with
  | Leaf -> accu
  | Node (l, k, e, _, r) -> fold_left f r (f k e (fold_left f l accu))
let rec fold_right (f: 'a -> 'b -> 'c -> 'c) (t: ('a, 'b) t) (accu: 'c): 'c =
  match t with
  | Leaf -> accu
  | Node (l, k, e, _, r) -> fold_right f l (f k e (fold_right f r accu))
let fold = fold_right

(** Extremal elements *)
let rec min_binding (t: ('a, 'b) t): 'a * 'b =
  match t with
  | Leaf -> raise Not_found
  | Node (Leaf, k, e, _, _) -> (k, e)
  | Node (l, _, _, _, _) -> min_binding l
let min_key (t: ('a, 'b) t): 'a = fst (min_binding t)
let choose = min_binding


(** Printing *)
let t_2str
    (emp: string) (* string value of the empty structure *)
    (sep: string) (* separator between two entries *)
    (f: 'key -> 'a -> string) (* printing of one element *)
    (t: ('key, 'a) t): string = 
  if is_empty t then emp
  else 
    let k, a = choose t in
    let t = remove k t and start = f k a in
    fold (fun k a s -> Printf.sprintf "%s%s%s" s sep (f k a)) t start  
 

(** Utilities *)
let rec size (t: ('a, 'b) t): int =
  match t with
  | Leaf -> 0
  | Node (l, _, _, _, r) -> 1 + size l + size r


(** Map2 functions *)
let rec map2 (cmp: 'a -> 'a -> int) (f: 'a -> 'a -> 'a)
    : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t =
  let rec aux tl tr =
    if tl == tr then tl
    else
      match tl, tr with
      | Leaf, Leaf -> Leaf
      | Node (tll, tlk, tle, tli, tlr), Node (trl, trk, tre, tri, trr) ->
          (* we need to see what kind of splitting we need *)
          failwith "node,node"
      | _, _ -> failwith "map2: heterogeneous state" in
  aux
