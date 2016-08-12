(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: bound_set.ml
 **       A naive implementation of bounds, as sets of offsets
 ** Xavier Rival, Pascal Sotin, 2012/04/29 *)
open Data_structures
open Lib
open Nd_sig
open Off_sig
open Offs

(** Error report *)
module Log =
  Logger.Make(struct let section = "b_set___" and level = Log_level.DEBUG end)

(* Internal debug flag *)
let debug_loc = false

(** A bound is composed of a main offset,
 ** and a set of alternate descriptions, that are necessarily equal *)
type t = { b_main: Offs.t;
           b_alt:  OffSet.t; }
(* Size is the same as in the module Offs *)
type size = Offs.size

(** Printing *)
let t_2str (b: t): string =
  let s =
    OffSet.fold
      (fun o acc ->
        Printf.sprintf "%s; %s" acc (Offs.t_2str o)
      ) b.b_alt (Offs.t_2str b.b_main) in
  Printf.sprintf "{ %s }" s

(** Iterators, used internally *)
(* Cardinal *)
let cardinal (b: t): int = 1 + OffSet.cardinal b.b_alt
(* Fold *)
let fold (f: Offs.t -> 'a -> 'a) (b: t) (acc: 'a): 'a =
  OffSet.fold f b.b_alt (f b.b_main acc)
(* Map *)
let map (f: Offs.t -> Offs.t) (b: t): t =
  { b_main = f b.b_main;
    b_alt  = OffSet.fold (fun o -> OffSet.add (f o)) b.b_alt OffSet.empty }

(** Constructors *)
(* From an offset *)
let of_offs (o: Offs.t): t = { b_main = o;
                               b_alt  = OffSet.empty }
(* From a set of offsets *)
let of_offset (os: OffSet.t): t =
  if os = OffSet.empty then Log.fatal_exn "of_offset of empty set"
  else
    let omin = OffSet.min_elt os in
    { b_main = omin;
      b_alt  = OffSet.remove omin os }
(* Null offset *)
let zero: t = of_offs Offs.zero
(* Integer offset *)
let of_int (i: int): t = of_offs (Offs.of_int i)
(* String offset *)
let of_string (s: string): t = of_offs (Offs.of_string s)
(* Field (string+int) offset *)
let of_field (f: string * int): t = of_offs (Offs.of_field f)
(* From a numerical domain expression *)
let of_n_expr (e: n_expr): t = of_offs (Offs.of_n_expr e)

(** Extraction *)
(* To offset *)
let to_offs (b: t): Offs.t = b.b_main
(* To list of offsets *)
let to_off_list (b: t): Offs.t list =
  OffSet.fold (fun x y -> x :: y) b.b_alt [ b.b_main ]

(** Merging *)
(* Fusion of to bounds that were discovered equal *)
let merge (b0: t) (b1: t): t =
  (* new main element, and main element that is not main anymore if any *)
  let main, other =
    let c = Offs.compare b0.b_main b1.b_main in
    if c < 0 then b0.b_main, Some b1.b_main
    else if c > 0 then b1.b_main, Some b0.b_main
    else b0.b_main, None in
  (* fold to compute alternate representations *)
  let alt =
    let set0 =
      match other with
      | None   -> b1.b_alt
      | Some o -> OffSet.add o b1.b_alt in
    OffSet.fold OffSet.add b0.b_alt set0 in
  { b_main = main;
    b_alt  = alt }

(** Intersection *)
(* Preserves only the bounds present in both sides (used in submem) *)
let inter (b0: t) (b1: t): t =
  let os0 = OffSet.add b0.b_main b0.b_alt
  and os1 = OffSet.add b1.b_main b1.b_alt in
  of_offset (OffSet.inter os0 os1)

(** Comparisons *)
(* Whether an offset is constant *)
let t_is_const (b: t): bool = Offs.t_is_const b.b_main
(* Compare, syntactic on AST, to build sets
 *  (the result does not necessarily have a semantic meaning) *)
let compare (b0: t) (b1: t): int =
  let r =
    let c = Offs.compare b0.b_main b1.b_main in
    if c = 0 then
      let sz0 = OffSet.cardinal b0.b_alt and sz1 = OffSet.cardinal b1.b_alt in
      let c = sz0 - sz1 in
      if c = 0 then
        if sz0 != 0 then
          let r0 = ref b0.b_alt and r1 = ref b1.b_alt and res = ref 0 in
          (* repeatedly extract least element and compare *)
          while !res = 0 && !r0 != OffSet.empty && !r1 != OffSet.empty do
            let lo0 = OffSet.min_elt !r0 and lo1 = OffSet.min_elt !r1 in
            res := Offs.compare lo0 lo1;
            if !res = 0 then
              begin
                r0 := OffSet.remove lo0 !r0;
                r1 := OffSet.remove lo1 !r1;
              end;
          done;
          !res
        else c (* both are empty sets, equal *)
      else c (* greater size is higher *)
    else c (* greater main offset is higher *) in
  if debug_loc then (* turn on, when debugging needed *)
    Log.info "bounds comparison:\n - %s\n - %s\n=> %d"
      (t_2str b0) (t_2str b1) r;
  r
(* Equality test *)
let eq (b0: t) (b1: t): bool = compare b0 b1 = 0
(* Compatibility test *)
let compat (b0: t) (b1: t): t option =
  if Offs.compare b0.b_main b1.b_main = 0 then
    Some { b0 with b_alt = OffSet.inter b0.b_alt b1.b_alt }
  else if OffSet.mem b0.b_main b1.b_alt then
    Some { b1 with b_alt = OffSet.inter b0.b_alt b1.b_alt }
  else if OffSet.mem b1.b_main b0.b_alt then
    Some { b0 with b_alt = OffSet.inter b0.b_alt b1.b_alt }
  else None
(* Compare, semantic *)
let leq (sat: (n_cons -> bool)) (b0: t) (b1: t): bool =
  let r =
    fold
      (fun (o0: Offs.t) (acc: bool option) ->
        match acc with
        | None | Some false ->
            fold
              (fun (o1: Offs.t) acc ->
                match acc with
                | None | Some false -> Some (Offs.leq sat o0 o1)
                | _ -> acc
              ) b1 acc
        | Some true -> acc
      ) b0 None in
  match r with
  | None -> false
  | Some b -> b
(* Nullness test *)
let is_zero (b: t): bool =
  fold (fun o acc -> acc || Offs.is_zero o) b false
(* Semantic comparison of bounds:
 *  - returns Some i (i \in {-1,0,1}) if it can be decided
 *  - otherwise, returns None *)
let t_order (sat: n_cons -> bool) (b0: t) (b1: t): int option =
  fold
    (fun (o0: Offs.t) (acc: int option) ->
      if acc = None then
        fold
          (fun (o1: Offs.t) (acc: int option) ->
            if acc = None then Offs.t_order sat o0 o1
            else acc
          ) b1 acc
      else acc
    ) b0 None

(** Arithmetics *)
let add_int (b: t) (i: int): t = map (fun o -> Offs.add_int o i) b
let bin (f: Offs.t -> Offs.t -> Offs.t) (b0: t) (b1: t): t =
  let main = f b0.b_main b1.b_main in
  let set =
    fold
      (fun o0 acc ->
        fold (fun o1 acc -> OffSet.add (f o0 o1) acc) b1 acc
      ) b0 OffSet.empty in
  { b_main = main;
    b_alt  = OffSet.remove main set }
let add: t -> t -> t = bin Offs.add
let add_size (b: t) (s: size): t = map (fun o -> Offs.add_size o s) b
let sub (b0: t) (b1: t): size = Offs.sub b0.b_main b1.b_main
let sub_t: t -> t -> t = bin Offs.sub_t
let mul_int (b: t) (i: int): t = map (fun o -> Offs.mul_int o i) b
(* Split a bound modulo some given stride *)
let modulo_split (stride: int) (bnd: t): (t * t) (* aligned + bias *) =
  let f_off = Offs.modulo_split stride in
  let i_main, m_main = f_off bnd.b_main in
  let i_alt, m_alt =
    OffSet.fold
      (fun o (acci, accm) ->
        let i_o, m_o = f_off o in
        OffSet.add i_o acci, OffSet.add m_o accm
      ) bnd.b_alt (OffSet.empty, OffSet.empty) in
  { b_main = i_main;
    b_alt  = OffSet.remove i_main i_alt },
  { b_main = m_main;
    b_alt  = OffSet.remove m_main m_alt }
(* Checks whether is aligned on stride *)
let is_on_stride (stride: int) (bnd: t): bool =
  try
    let f o = if Offs.is_on_stride stride o then raise Stop in
    f bnd.b_main;
    OffSet.iter f bnd.b_alt;
    false
  with
  | Stop -> true

(** Utilities *)
(* Ids of symbolic variables *)
let t_sym_var_ids_add (acc: IntSet.t) (b: t): IntSet.t =
  fold (fun (o: Offs.t) (acc: IntSet.t) -> Offs.t_sym_var_ids_add acc o) b acc

(** Construction from a list of offsets *)
let of_offs_list (l: Offs.t list): t =
  match l with
  | [ ] -> Log.fatal_exn "of_offs_list: empty"
  | a :: b ->
      List.fold_left
        (fun acc o ->
          let c = Offs.compare o acc.b_main in
          if c < 0 then (* we found a new main element *)
            { b_main = o;
              b_alt  = OffSet.add acc.b_main acc.b_alt }
          else if c > 0 then (* we found another alternative element *)
            { acc with
              b_alt  = OffSet.add o acc.b_alt }
          else (* no need to add the element *)
            acc
        ) { b_main = a;
            b_alt  = OffSet.empty } b

(** Unification *)
let pre_unify (b0: t) (b1: t): (int * int * int) list * Offs.t list =
  fold
    (fun o0 acc ->
      fold
        (fun o1 acc ->
          match Offs.t_unify o0 o1 with
          | None -> acc
          | Some (l, o) ->
              let l0 = fst acc in
              if List.length l0 + List.length l <= 1 then
                l @ l0, o :: snd acc
              else
                begin
                  (* we do not check compatibility of unifications yet *)
                  Log.warn "throwing unification";
                  acc
                end
        ) b1 acc
    ) b0 ([ ], [ ])
let unify (b0: t) (b1: t): (int * int * int) list * t =
  let l_unif, l_folds = pre_unify b0 b1 in
  l_unif, of_offs_list l_folds
(* Unification of all offsets in a pair of bounds:
 *  Ideally, we should assert equality between all pairs of offsets in both
 *  bounds, but we compute a conservative approximation of this
 *  - if each bound has only a main, unify them
 *  - if each bound has a main and a secondary, unify the pair of main offsets,
 *    and the pair of secondary offsets
 *  - if both bounds have the same number of offsets, but that number is
 *    greater than two, unify them pair by pair, in their order (hopefully
 *    similar offsets will get unified, and this will produce more information
 *  - in all other cases, rely on pre-unify, that tries to consider all the
 *    pairs, but will drop cases that do not unify well...
 *)
let unify_all (b0: t) (b1: t): ((int * int * int) list * t) option =
  let c0 = cardinal b0 and c1 = cardinal b1 in
  if c0 = 1 && c1 = 1 then
    let l_unif, l_folds = pre_unify b0 b1 in
    match l_folds with
    | [ ] -> None
    | [ a ] -> Some (l_unif, of_offs a)
    | _ -> Log.fatal_exn "unbound multiple unifiers"
  else if c0 = c1 then
    let l_unif, l_folds =
      List.fold_left2
        (fun acc o0 o1 ->
          match Offs.t_unify o0 o1 with
          | None -> acc
          | Some (l, o) ->
              let l0 = fst acc in
              if List.length l0 + List.length l <= 1 then
                l @ l0, o :: snd acc
              else
                begin
                  (* we do not check compatibility of unifications yet *)
                  Log.warn "throwing unification";
                  acc
                end
        ) ([ ], [ ]) (to_off_list b0) (to_off_list b1) in
    match l_folds with
    | [ ] -> None
    | _ -> Some (l_unif, of_offs_list l_folds)
  else
    begin
      Log.warn "UNIFIER (%d-%d): %s   ===   %s"
        (cardinal b0) (cardinal b1) (t_2str b0) (t_2str b1);
      let l_unif, l_folds = pre_unify b0 b1 in
      match l_folds with
      | [ ] -> None
      | _ -> Some (l_unif, of_offs_list l_folds)
    end

(** Rename *)
let rename (index: int IntMap.t) (b: t): t =
  let l_renamed = fold (fun o acc -> Offs.t_rename index o :: acc) b [ ] in
  of_offs_list l_renamed
