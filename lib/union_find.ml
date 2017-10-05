(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: union_find.ml
 **       Union-Find data structure
 ** Antoine Toubhans, 2013/04/11 *)
open Lib

(** Error report *)
module Log =
  Logger.Make(struct let section = "ufind___" and level = Log_level.DEBUG end)

(* Flags *)
let flag_do_control: bool = true

(* Main type *)
type 'a t = ('a, 'a) Bi_fun.t

let t_2stri (ind: string) (f: 'a -> string) (x: 'a t): string =
  Bi_fun.t_2str ind f f x

(* Sanity check *)
let sanity_check (mess: string) (x: 'a t): unit = 
  Bi_fun.sanity_check ("union_find: "^mess) x;
  (* Checks that there are no cycles in the graph *)
  let check:'a -> unit = 
    let rec aux set a =
      let b = Bi_fun.image a x in
      if Aa_sets.mem b set then
        Log.fatal_exn "union find, sanity check failed: there is a cycle!"
      else
        if compare b a != 0 then aux (Aa_sets.add a set) b in
    aux Aa_sets.empty in
  Bi_fun.iter_dir (fun a _ -> check a) x        

(* Empty *)
let empty: 'a t = Bi_fun.empty

(* Mem, returns true if an element belongs to the structure *)
let mem (id: 'a) (t: 'a t): bool = Bi_fun.mem_dir id t

(* Is_representative, returns true iff an id is a representive *)
(* N.B. an element is a representative iff it is mapped to itself *)
let is_representative (id: 'a) (uf: 'a t): bool =
  let id1 = Bi_fun.image id uf in id = id1

(* Add, add a new element, take a representative as optional argument *)
let add (id: 'a) ?(rep: 'a = id) (uf: 'a t): 'a t =
  assert (not flag_do_control || not (Bi_fun.mem_dir id uf));
  assert (not flag_do_control || id = rep || is_representative rep uf);
  Bi_fun.add id rep uf

(* Change a representative, returns None if unable to do so *)
let change_representative (r: 'a) (uf: 'a t): ('a * 'a t) option = 
  assert (not flag_do_control || is_representative r uf);
  let inv = Bi_fun.inverse r uf in
  let inv_r = Aa_sets.remove r inv in
  try 
    let r0 = Aa_sets.choose inv_r in
    let uf = Aa_sets.fold (fun id -> Bi_fun.add id r0) inv uf in 
    Some (r0, uf)
  with Not_found -> None

(* Rem, remove an element,
 * returns another element of its class if there exists so *)
let rem (id: 'a) (uf: 'a t): 'a option * 'a t =
  assert (not flag_do_control || Bi_fun.mem_dir id uf);
  let id1 = Bi_fun.image id uf in
  if compare id id1 != 0 then (* id is not a representative *)
    let rev_id = Bi_fun.inverse id uf in
    let uf = Aa_sets.fold (fun id -> Bi_fun.add id id1) rev_id uf in
    Some id1, Bi_fun.rem_dir id uf
  else (* then id is a representative *)
    match change_representative id uf with
    | Some (new_rep, uf) -> Some new_rep, Bi_fun.rem_dir id uf
    | None               -> None, Bi_fun.rem_dir id uf

(* Rem_class, remove a whole class, given its representative element *)
let rem_class (r: 'a) (uf: 'a t): 'a t =
  assert (not flag_do_control || is_representative r uf);
  let rec aux uf = function
    | [] -> uf
    | set :: acc_todo ->
        let uf, acc_todo =
          Aa_sets.fold
            (fun id (uf, acc_todo) ->
              let rev_id = Bi_fun.inverse id uf in
              Bi_fun.rem_dir id uf, rev_id::acc_todo
            ) set (uf, acc_todo) in
        aux uf acc_todo in
  aux uf [ Aa_sets.singleton r ]

(* Find, returns the representative of the class of a given element
 * the returned union-find element is for path compression *)
let rec find (id: 'a) (uf: 'a t): 'a * 'a t =
  let id1 = Bi_fun.image id uf in
  if id = id1 then id, uf
  else
    let r, uf1 = find id1 uf in
    r, Bi_fun.add id r uf1

(* find_class, returns the class that has a given representative *)
let find_class (r: 'a) (uf: 'a t): 'a list =
  let rec aux acc = function
    | [] -> acc
    | set :: acc_todo ->
        let acc, acc_todo = 
          Aa_sets.fold
            (fun id (acc, acc_todo) ->
              assert (not flag_do_control || not (List.mem id acc));
              let rev_id = Bi_fun.inverse id uf in
              id::acc, rev_id::acc_todo
            ) set (acc, acc_todo) in
        aux acc acc_todo in
  assert (not flag_do_control || is_representative r uf);
  aux [ r ] [ Aa_sets.remove r (Bi_fun.inverse r uf) ]

(* lift an element to the representive of a class *)
let lift_rep (id: 'a) (uf: 'a t): 'a t =
  let rep,uf = find id uf in
  if rep = id then
    uf
  else
    Bi_fun.add id id (Bi_fun.add rep id uf)


(* Union r1 r2, merges two classes, given their representatives r1 and r2;
 * r1 remains a representative, r2 does not *)
let union (r1: 'a) (r2: 'a) (uf: 'a t): 'a t = 
  assert (not flag_do_control || is_representative r1 uf);
  assert (not flag_do_control || is_representative r2 uf);
  if r1 = r2 then uf else Bi_fun.add r2 r1 uf


(* Classes meet ? *)
let is_same_class
    (l: 'a) (r: 'a) (au: 'a t): bool =
  mem l au && mem r au && fst (find l au) = fst (find r au)

let fold (f: 'a -> 'b -> 'b) (base: 'a t) (acc: 'b): 'b =
  Bi_fun.fold_dom (fun a _ -> f a) base acc

let meet (ufl: 'a t) (ufr: 'a t): 'a t =
  let is_eq (a: 'a) (b: 'a) =
    a != b && is_same_class a b ufl && is_same_class a b ufr in
  fold
    (fun a acc ->
      fold
        (fun ia iacc ->
          if is_eq a ia && not (mem a iacc && mem ia iacc) then
            let a,iacc =
              if mem a iacc then find a iacc
              else (a, add a iacc) in
            let ia,iacc =
              if mem ia iacc then
                find ia iacc
              else (ia, add ia iacc) in
            union a ia iacc
          else
            iacc
        ) ufl acc
    ) ufl empty

(** Lattice operation *)

(* Rename one variable *)
let var_rename (i: 'a) (j: 'a) (uf: 'a t): 'a t =
  try
    let k = Bi_fun.image i uf in
    let set = Bi_fun.inverse i uf in
    let uf = Aa_sets.fold (fun k -> Bi_fun.rem_dir k) set uf in
    let uf = Aa_sets.fold (fun k -> Bi_fun.add k j) set uf in
    Bi_fun.add j (if i = k then j else k) (Bi_fun.rem_dir i uf)
  with Not_found -> Log.fatal_exn "UnionFind, var_rename: element not found!"

(* Is_le, Point-wise inclusion checking, returns a function
 * from R representatives to L representative if successful *)
let is_le (uf_l: 'a t) (uf_r: 'a t): ('a, 'a) Aa_maps.t option =
  try
    let f = 
      Bi_fun.fold_dom
        (fun i _ f -> 
          let rep_l, _ = find i uf_l
          and rep_r, _ = find i uf_r in
          try 
            let rep0_l = Aa_maps.find rep_r f in
            if rep0_l = rep_l then f else raise Stop
          with Not_found -> Aa_maps.add rep_r rep_l f
        ) uf_r Aa_maps.empty in
    Some f
  with Stop -> None
