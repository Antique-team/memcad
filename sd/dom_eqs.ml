(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_eqs.ml
 **       equalities between two sets of variables
 ** Antoine Toubhans, 2013/12/02 *)
open Lib

(** Error report *)
module Log =
  Logger.Make(struct let section = "d_eqs___" and level = Log_level.DEBUG end)

(** Main type *)

(* Equalities between elements of type 'a and elements of type 'b *)
type ('a, 'b) t =
    { (* bijection between representative of classes that are equals *)
      t_bij:    ('a, 'b) Bi_fun.t; 
      (* partitions of 'a *)
      t_part_a: 'a Union_find.t;  
      (* partitions of 'b *)
      t_part_b: 'b Union_find.t }

(* Empty set of equalities *)
let empty: ('a, 'b) t = 
  { t_bij    = Bi_fun.empty_inj; 
    t_part_a = Union_find.empty;
    t_part_b = Union_find.empty }

(* Pretty printing *)
let t_2stri 
    (a_2str: 'a -> string) (b_2str: 'b -> string)
    (ind: string) (t: ('a, 'b) t): string = 
  Bi_fun.fold_dom
    (fun ra rb -> 
      let l_a = Union_find.find_class ra t.t_part_a
      and l_b = Union_find.find_class rb t.t_part_b in
      Printf.sprintf "%s{ %s }\t<->\t{ %s }\n%s" ind
        (gen_list_2str "empty" a_2str "," l_a)
        (gen_list_2str "empty" b_2str "," l_b)
        ) t.t_bij ""

(* Sanity check *)
let sanity_check (mess: string) (x: ('a, 'b) t): unit =
  Bi_fun.sanity_check "dom_eqs, t_bij" x.t_bij;
  Union_find.sanity_check "dom_eqs, t_part_a" x.t_part_a;
  Union_find.sanity_check "dom_eqs, t_part_b" x.t_part_b;
  (* checks that each element in t_bij component is a
   * representative in the union-find structures *)
  Bi_fun.iter_dir
    (fun a b ->
      if not (Union_find.is_representative a x.t_part_a) then
        Log.fatal_exn "%s: an 'a-element is not a representative" mess;
      if not (Union_find.is_representative b x.t_part_b) then
        Log.fatal_exn "%s: an 'b-element is not a representative" mess
    ) x.t_bij

(** Read equalities *)

(* Are two element equal *)
let are_eq (a: 'a) (b: 'b) (x: ('a, 'b) t): bool =
  Union_find.mem a x.t_part_a &&
  Union_find.mem b x.t_part_b &&
  ( 
  let rep_a, _ = Union_find.find a x.t_part_a
  and rep_b, _ = Union_find.find b x.t_part_b in
  rep_b = Bi_fun.image rep_a x.t_bij
  )

(* Find a "b" element that is equal to an "a" element *)
let find_eq_a (a: 'a) (x: ('a, 'b) t): 'b option = 
  try
    let r, _ = Union_find.find a x.t_part_a in
    Bi_fun.image_opt r x.t_bij
  with Not_found -> None

(* Find an "a" element that is equal to a "b" element *)
let find_eq_b (b: 'b) (x: ('a, 'b) t): 'a option = 
  try
    let r, _ = Union_find.find b x.t_part_b in
    Some (Bi_fun.inverse_inj r x.t_bij)
  with Not_found -> None

(** Write / Unwrite equalities *)

(* Write equality [a=b] *)
let write_eq (a: 'a) (b: 'b) (x: ('a, 'b) t): ('a, 'b) t =
  match
    Union_find.mem a x.t_part_a,
    Union_find.mem b x.t_part_b with
  | true, true   -> 
      let ra, tpa = Union_find.find a x.t_part_a
      and rb, tpb = Union_find.find b x.t_part_b in
      let rb0 = Bi_fun.image ra x.t_bij in
      if rb0 = rb then (* already equal *) x
      else
        let ra0 = Bi_fun.inverse_inj rb x.t_bij in
        { t_bij    = Bi_fun.rem_dir ra0 x.t_bij;
          t_part_a = Union_find.union ra ra0 tpa;
          t_part_b = Union_find.union rb0 rb tpb; }
  | true, false  ->
      let ra, tpa = Union_find.find a x.t_part_a in
      let rb = Bi_fun.image ra x.t_bij in
      { x with
        t_part_a = tpa;
        t_part_b = Union_find.add b ~rep: rb x.t_part_b }
  | false, true  -> 
      let rb, tpb = Union_find.find b x.t_part_b in
      let ra = Bi_fun.inverse_inj rb x.t_bij in
      { x with
        t_part_a = Union_find.add a ~rep: ra x.t_part_a;
        t_part_b = tpb }
  | false, false ->
      { t_bij    = Bi_fun.add a b x.t_bij;
        t_part_a = Union_find.add a x.t_part_a;
        t_part_b = Union_find.add b x.t_part_b }

(* Forget about an "a" element *)
let forget_a (a: 'a) (x: ('a, 'b) t): ('a, 'b) t =
  if Union_find.mem a x.t_part_a then
    match Bi_fun.image_opt a x.t_bij with
    | None -> (* a is not a representative *)
        let _, tpa = Union_find.rem a x.t_part_a in
        { x with
          t_part_a = tpa }
    | Some b -> (* a is a representative *)
        begin
          match Union_find.rem a x.t_part_a with
          | None, tpa -> (* [a] class was {a} *)
              { t_bij    = Bi_fun.rem_dir a x.t_bij;
                t_part_a = tpa;
                t_part_b = Union_find.rem_class b x.t_part_b }
          | Some aa, tpa -> (* representative has changed *)
              let new_rep, tpa = Union_find.find aa tpa in
              { t_bij    = Bi_fun.add new_rep b (Bi_fun.rem_dir a x.t_bij);
                t_part_a = tpa;
                t_part_b = x.t_part_b }
        end
  else x

(* Forget about a "b" element *)
let forget_b (b: 'b) (x: ('a, 'b) t): ('a, 'b) t =
  if Union_find.mem b x.t_part_b then
    if Bi_fun.mem_inv b x.t_bij then
      (* b is a representative *)
      let a = Bi_fun.inverse_inj b x.t_bij in      
      match Union_find.rem b x.t_part_b with
      | None, tpb -> (* [b] class was {b} *)
          { t_bij    = Bi_fun.rem_dir a x.t_bij;
            t_part_a = Union_find.rem_class a x.t_part_a;
            t_part_b = tpb }
      | Some bb, tpb -> (* representative has changed *)
          let new_rep, tpb = Union_find.find bb tpb in
          { t_bij    = Bi_fun.add a new_rep (Bi_fun.rem_dir a x.t_bij);
            t_part_a = x.t_part_a;
            t_part_b = tpb }
    else (* b is not a representative *)
      let _, tpb = Union_find.rem b x.t_part_b in
      { x with
        t_part_b = tpb }
  else x

(** Iterators *)

(* Iter, over equivalence classes *)
let iter (f: 'a list -> 'b list -> unit) (x: ('a, 'b) t): unit =
  Bi_fun.iter_dir
    (fun a b ->
      let cl_a = Union_find.find_class a x.t_part_a
      and cl_b = Union_find.find_class b x.t_part_b in
      f cl_a cl_b
    ) x.t_bij

(* Fold, over equivalence classes *)
let fold (f: 'a list -> 'b list -> 'c -> 'c) (x: ('a, 'b) t): 'c -> 'c =
  Bi_fun.fold_dom
    (fun a b ->
      let cl_a = Union_find.find_class a x.t_part_a
      and cl_b = Union_find.find_class b x.t_part_b in
      f cl_a cl_b
    ) x.t_bij
