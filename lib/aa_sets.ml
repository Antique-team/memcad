(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: aa_sets.ml
 **       Arne Anderson implementation for polymorphic sets
 ** Xavier Rival, 2012/11/16 *)

type 'a t = ('a, unit) Aa_maps.t

(** Basic functions (accesses, add, remove) *)
(* Empty element *)
let empty: 'a t = Aa_maps.empty
(* Emptiness test *)
let is_empty = Aa_maps.is_empty
(* Membership test *)
let mem: 'a -> 'a t -> bool = Aa_maps.mem
(* Adding an element *)
let add (x: 'a) (t: 'a t): 'a t = Aa_maps.add x () t
(* Removing an element *)
let remove: 'a -> 'a t -> 'a t = Aa_maps.remove

(** Iterators *)
let iter (f: 'a -> unit) (t: 'a t): unit =
  let ff k () = f k in
  Aa_maps.iter ff t
let fold (f: 'a -> 'b -> 'b) (t: 'a t) (accu: 'b): 'b =
  let ff k () acc = f k acc in
  Aa_maps.fold ff t accu

(** Extremal elements *)
let choose = Aa_maps.min_key
let min_elt = Aa_maps.min_key

(** Set operations *)
let singleton (x: 'a): 'a t = add x empty
let cardinal (t: 'a t): int = Aa_maps.size t
let union (t: 'a t) (u: 'a t): 'a t = fold add t u
let exists (f: 'a -> bool) (t: 'a t): bool = fold (fun x b -> b || f x) t false
let filter (f: 'a -> bool) (t: 'a t): 'a t =
  fold (fun x accu -> if f x then add x accu else accu) t empty
let for_all (f: 'a -> bool) (t: 'a t): bool = fold (fun x b -> b && f x) t true
let subset (t: 'a t) (u: 'a t): bool =
  fold (fun x accu -> accu && mem x u) t true
let equal (t: 'a t) (u: 'a t): bool =
  cardinal t = cardinal u && subset t u

let rec fold_subset (f: 'a t -> 'b -> 'b) (s: 'a t) (b: 'b): 'b =  
  fold (fun a -> fold_subset f (remove a s)) s (f s b)

(** Printing *)
let t_2str
    (sep: string) (* separator between two entries *)
    (f: 'a -> string) (t: 'a t): string = 
  if is_empty t then ""
  else 
    let a = choose t in
    let t = remove a t and start = f a in
    fold (fun a s -> Printf.sprintf "%s%s%s" s sep (f a)) t start
