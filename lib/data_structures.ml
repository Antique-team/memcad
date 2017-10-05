(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: data_structures.ml
 **       basic declarations of data structures
 ** Xavier Rival, 2011/05/19 *)

(** Interface to introspect the abstract domain configuration *)
module type NAME = sig
  val module_name: string
end
module type CONFIG_2STR = sig
  val config_2str: unit -> string
end
module type INTROSPECT = sig
  include NAME
  include CONFIG_2STR
end

(** Tuples *)
let fst3 (a, _, _) = a
let trd3 (_, _, a) = a


(** Option types *)
module Option =
  struct
    let map (f: 'a -> 'b): 'a option -> 'b option = function
      | Some x -> Some (f x)
      | None -> None
    let get: 'a option -> 'a = function
      | Some x -> x
      | None -> raise (Invalid_argument "Option.get")
    let get_default (def: 'a): 'a option -> 'a = function
      | None -> def
      | Some x -> x
  end

(** Maps and Sets with printers *)
module type OrderedType =
  sig
    include Set.OrderedType
    val t_2str: t -> string
  end
module type SET =
  sig
    include Set.S
    val to_list: t -> elt list
    val t_2str: string -> t -> string
  end
module type MAP =
  sig
    include Map.S
    val t_2str: string -> ('a -> string) -> 'a t -> string
    val update: key -> 'a -> 'a t -> 'a t
    (* Find functions with specific behavior if key absent *)
    val find_err: string -> key -> 'a t -> 'a
    val find_val: 'a -> key -> 'a t -> 'a
    val find_comp: (unit -> 'a) -> key -> 'a t -> 'a
    (* Union, for compatibility *)
    val union: (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
  end
module SetMake = functor (O: OrderedType) ->
  struct
    include Set.Make( O )
    let to_list (t: t): elt list =
      fold (fun a acc -> a :: acc) t [ ]
    let t_2str (sep: string) (t: t): string =
      let b = ref true in
      fold
        (fun i acc ->
          let locsep = if !b then "" else sep in
          b := false;
          Printf.sprintf "%s%s%s" acc locsep (O.t_2str i)
        ) t ""
    (* return the min element of 's' and 's' without it *)
    let pop_min s =
      let mini = min_elt s in
      let others = remove mini s in
      (mini, others)
  end
module MapMake = functor (O: OrderedType) ->
  struct
    include Map.Make( O )
    let t_2str (sep: string) (f_2str: 'a -> string) (t: 'a t): string =
      let b = ref true in
      fold
        (fun i x acc ->
          let locsep = if !b then "" else sep in
          b := false;
          Printf.sprintf "%s%s%s => %s" acc locsep (O.t_2str i) (f_2str x)
        ) t ""
    let update k v m =
      add k v (remove k m)
    (* Find functions with specific behavior if key absent *)
    exception MapErr of string
    let find_err (msg: string) (k: key) (t: 'a t): 'a =
      try find k t
      with Not_found -> raise (MapErr (Printf.sprintf "Map.Not_found: %s" msg))
    let find_val (v: 'a) (k: key) (t: 'a t): 'a =
      try find k t with Not_found -> v
    let find_comp (f: unit -> 'a) (k: key) (t: 'a t): 'a =
      try find k t with Not_found -> f ( )
    let keys (m: 'a t): key list =
      List.map fst (bindings m)
    let values (m: 'a t): 'a list =
      List.map snd (bindings m)
    (* Union, for compatibility *)
    let union f m0 m1 =
      fold
        (fun k x0 acc ->
          if mem k m1 then
            let x1 = find k m1 in
            match f k x0 x1 with
            | Some x -> add k x acc
            | None   -> raise (MapErr "union=>none")
          else add k x0 acc
        ) m0 m1
  end


(** Construction of standard data-structures *)
module IntOrd =
  struct
    type t = int
    let compare = Pervasives.compare
    let t_2str = string_of_int
  end
module StringOrd =
  struct
    type t = string
    let compare = compare
    let t_2str x = x
  end

module IntMap =
  struct
    include MapMake(IntOrd)
    let of_list l =
      List.fold_left (fun acc (k, v) -> add k v acc) empty l
  end
module IntSet    =
  struct
    include SetMake(IntOrd)
  end
module StringMap = MapMake(StringOrd)
module StringSet =
  struct
    include SetMake(StringOrd)
    let of_list (l: string list) =
      List.fold_left (fun acc s -> add s acc) empty l
  end


(** Pairs of integers; used for graphs *)
module PairOrd =
  struct
    type t = int * int
    let compare (i0,i1) (j0,j1) =
      let c0 = i0 - j0 in
      if c0 = 0 then i1 - j1
      else c0
    let t_2str (x,y) = Printf.sprintf "(%d,%d)" x y
  end
module PairMap = MapMake( PairOrd )
module PairSet =
  struct
    include SetMake( PairOrd )
    (* convert a PairSet.t to a graph node label string;
     * creates a string such as "{o0@n231, o0@n243}" *)
    let node_label ps =
      let buff = Buffer.create 80 in
      let started = ref false in
      Buffer.add_string buff "{";
      iter
        (fun (offs, uid) ->
          if !started then Buffer.add_string buff ", "
          else started := true;
          Buffer.add_string buff (Printf.sprintf "o%d@n%d" offs uid)
        ) ps;
      Buffer.add_string buff "}";
      Buffer.contents buff
  end

(* Set of pairs set *)
 module PairOrdSet =
  struct
    type t = PairSet.t
    let compare t1 t2 =
      PairSet.compare t1 t2
    let t_2str t = Printf.sprintf "{%s}" (PairSet.t_2str "," t)
  end
module PairSetSet = 
  struct
    include SetMake( PairOrdSet )
    let node_labels pss =
      fold
        (fun ps acc ->
          (PairSet.node_label ps) :: acc
        ) pss []
  end
module PairSetMap = MapMake( PairOrdSet )

(** Polymorphic maps *)
module PMap = Aa_maps
module PSet = Aa_sets

module List =
  struct
    include List
    (* find first index of x in l or raise Not_found *)
    let index x l =
      let rec loop i = function
        | [] -> raise Not_found
        | y :: ys ->
            if x = y then i
            else loop (i + 1) ys in
      loop 0 l
    let fold = fold_left
    let fold_lefti (f: int -> 'a -> 'b -> 'a) (x: 'a) (l: 'b list): 'a =
      let _i, res =
        List.fold_left
          (fun (i, acc) x -> (i + 1, f i acc x))
          (0, x) l in
      res
    let nthd (f: unit -> 'a) (l: 'a list) (n: int): 'a =
      try List.nth l n
      with Failure _ -> f ( )
    let map_flatten (f: 'a -> 'b list) (l: 'a list): 'b list =
      List.flatten (List.map f l)
  end

module String =
  struct
    include String
    (* rm first char of a string, if possible *)
    let pop s =
      if s = "" then
        raise (Invalid_argument "String.pop")
      else
        String.sub s 1 (String.length s - 1)
  end
