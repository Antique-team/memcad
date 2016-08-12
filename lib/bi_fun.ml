(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: bi_fun.ml
 **       Bi-directional representation of finite functions
 **       i.e., with both the function and its inverse
 ** Xavier Rival, 2013/07/20 *)
open Lib

(** Error report *)
module Log =
  Logger.Make(struct let section = "bifun___" and level = Log_level.DEBUG end)

(** The main data type *)
(* Finite function structure:
 * - t_dir:  direct image A -> B
 * - t_inv:  reverse image B -> P(A)
 * - t_inj:  whether it is supposed to describe an injective map
 *           then, sanity check or element addition will fail if
 *           injectivity is aobut to be broken *)
type ('a, 'b) t =
    { t_dir:  ('a, 'b) Aa_maps.t ;
      t_inv:  ('b, 'a Aa_sets.t) Aa_maps.t ;
      t_inj:  bool ; }

(** Emptiness *)
(* Empty, not assumed bijection *)
let empty = { t_dir = Aa_maps.empty ;
              t_inv = Aa_maps.empty ;
              t_inj = false }
(* Empty, assumed bijection (safety checks that it remains one) *)
let empty_inj = { t_dir = Aa_maps.empty ;
                  t_inv = Aa_maps.empty ;
                  t_inj = true }
(* Test *)
let is_empty (x: ('a, 'b) t): bool = x.t_dir = Aa_maps.empty

(** Pretty-printing *)
(* Simple pp, of only one table (for now) *)
let t_2str (ind: string) (fa: 'a -> string) (fb: 'b -> string)
    (x: ('a, 'b) t): string =
  if is_empty x then
    Printf.sprintf "%s{ 0 element }\n" ind
  else
    let s = Aa_maps.size x.t_dir in
    let f a b = Printf.sprintf "%s  %s => %s\n" ind (fa a) (fb b) in
    Printf.sprintf "%s{ %d element%s\n%s%s}\n" ind s (if s > 1 then "s" else "")
      (Aa_maps.t_2str "" "" f x.t_dir) ind
(* Full pretty-printing *)
let t_2strf (fa: 'a -> string) (fb: 'b -> string) (x: ('a, 'b) t): string =
  let fs s = Aa_sets.t_2str ", " fa s in
  let fdir a b = Printf.sprintf "  %s => %s\n" (fa a) (fb b) in
  let finv b s = Printf.sprintf "  %s => { %s }\n" (fb b) (fs s) in
  Printf.sprintf "Card: %d dir; %d inv\nFwd:\n%sBwd:\n%s"
    (Aa_maps.size x.t_dir) (Aa_maps.size x.t_inv)
    (Aa_maps.t_2str "" "" fdir x.t_dir) (Aa_maps.t_2str "" "" finv x.t_inv)

(** Sanity check *)
let sanity_check (ctx: string) (x: ('a, 'b) t): unit =
  let fail (msg: string) =
    Log.info "Bi_fun.sanity_check<%s,%s> fails" ctx msg;
    Log.fatal_exn "sanity check failure" in
  Aa_maps.iter
    (fun a b ->
      let s =
        try Aa_maps.find b x.t_inv
        with Not_found -> fail "reverse image 1" in
      if not (Aa_sets.mem a s) then fail "reverse image 2"
    ) x.t_dir;
  Aa_maps.iter
    (fun b s ->
      if s = Aa_sets.empty then fail "empty reverse image";
      Aa_sets.iter
        (fun a ->
          try
            if b != Aa_maps.find a x.t_dir then fail "reverse image 3"
          with Not_found -> fail "reverse image 4"
        ) s
    ) x.t_inv;
  if x.t_inj then
    Aa_maps.iter
      (fun _ s ->
        if Aa_sets.cardinal s != 1 then fail "injectivity"
      ) x.t_inv

(** Operations *)
(* Size *)
let size (x: ('a, 'b) t): int = Aa_maps.size x.t_dir
(* Membership *)
let mem_dir (a: 'a) (x: ('a, 'b) t): bool = Aa_maps.mem a x.t_dir
let mem_inv (b: 'b) (x: ('a, 'b) t): bool = Aa_maps.mem b x.t_inv
(* Direct image *)
let image (a: 'a) (x: ('a, 'b) t): 'b = Aa_maps.find a x.t_dir
let image_opt (a: 'a) (x: ('a, 'b) t): 'b option =
  try Some (image a x) with Not_found -> None
let whole_image (x: ('a, 'b) t): 'b Aa_sets.t =
  Aa_maps.fold (fun b _ -> Aa_sets.add b) x.t_inv Aa_sets.empty
(* Reverse image *)
let inverse (b: 'b) (x: ('a, 'b) t): 'a Aa_sets.t =
  try Aa_maps.find b x.t_inv with Not_found -> Aa_sets.empty
let inverse_opt (b: 'b) (x: ('a, 'b) t): 'a option =
  let s = inverse b x in
  if Aa_sets.cardinal s = 0 then None
  else Some (Aa_sets.min_elt s)
let inverse_inj (b: 'b) (x: ('a, 'b) t): 'a =
  if not x.t_inj then
    Log.fatal_exn "inverse_inj applied to non injective function";
  try Aa_sets.choose (Aa_maps.find b x.t_inv)
  with Not_found ->
    Log.fatal_exn "inverse_inj: applied to incorrect injective function"
(* Removal *)
let rem_dir (a: 'a) (x: ('a, 'b) t): ('a, 'b) t =
  try
    let b = Aa_maps.find a x.t_dir in
    let s =
      try Aa_maps.find b x.t_inv
      with Not_found -> Log.fatal_exn "rem: incorrect structure" in
    let ns = Aa_sets.remove a s in
    let ninv =
      if ns = Aa_sets.empty then Aa_maps.remove b x.t_inv
      else Aa_maps.add b ns x.t_inv in
    { x with
      t_dir = Aa_maps.remove a x.t_dir ;
      t_inv = ninv }
  with Not_found -> x (* the element was not in the function before *)
let rem_inv (b: 'b) (x: ('a, 'b) t): ('a, 'b) t =
  try
    let s = Aa_maps.find b x.t_inv in
    { x with
      t_dir = Aa_sets.fold (fun a -> Aa_maps.remove a) s x.t_dir;
      t_inv = Aa_maps.remove b x.t_inv }
  with Not_found -> x (* the element was not in the function before *)
(* Addition *)
let add (a: 'a) (b: 'b) (x: ('a, 'b) t): ('a, 'b) t =
  (* removal of previous binding
   * (needed to ensure that the reverse image invariant is maintained) *)
  let x = rem_dir a x in
  (* addition of new binding *)
  let s = inverse b x in
  if x.t_inj && s != Aa_sets.empty then
    Log.fatal_exn "add breaking injectivity";
  { x with
    t_dir = Aa_maps.add a b x.t_dir ;
    t_inv = Aa_maps.add b (Aa_sets.add a s) x.t_inv }

(** Fold operations **)
(* Iter on the domain *)
let iter_dir (f: ('a -> 'b -> unit)) (x: ('a, 'b) t): unit =
  Aa_maps.iter f x.t_dir
(* Fold on the domain *)
let fold_dom (f: 'a -> 'b -> 'c -> 'c) (x: ('a, 'b) t) (c: 'c): 'c =
  Aa_maps.fold f x.t_dir c
(* Fold on the image *)
let fold_inverse (f: ('b -> 'a Aa_sets.t -> 'c -> 'c)) (x: ('a, 'b) t)
    (c: 'c): 'c =
  Aa_maps.fold f x.t_inv c
