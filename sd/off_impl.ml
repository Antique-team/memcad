(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: off_impl.ml
 **       simple implementations of various forms of offsets
 ** Xavier Rival, 2012/04/23 *)
open Data_structures
open Lib
open Nd_sig
open Nd_utils
open Off_sig

module Log =
  Logger.Make(struct let section = "off_impl" and level = Log_level.DEBUG end)

(** The implementations of offsets given in this module are not used anymore
 ** as we use linexpr now, but we keep them just in case (we could need them
 ** for debugging). *)

(** Implementation with integer offsets:
 ** - this is the most basic choice, but now we use linexpr instead *)
module Off_Int =
  (struct
    (** Offsets and sizes are integers *)
    type t = int
    type size = int

    (** Printing *)
    let t_2str (o: t): string =
      Printf.sprintf "[o:@%d]" o
    let size_2str: size -> string = string_of_int

    (** Constructors and conversions *)
    (* Null offset *)
    let zero: t = 0
    let size_zero: size = 0
    (* Integer offset *)
    let of_int (i: int): t = i
    (* String offset *)
    let of_string (s: string): t =
      Log.fatal_exn "Off_Int implem, of_string %s" s
    (* Field (string+int) offset *)
    let of_field ((_, i): string * int): t = of_int i
    (* From a numerical domain expression *)
    let of_n_expr (e: n_expr): t =
      match e with
      | Ne_csti i -> i
      | _ ->
          Log.fatal_exn "Off_Int impl, of_n_expr: %s" (n_expr_2str e)
    (* Size, from an integer *)
    let size_of_int (i: int): size = i
    (* Size, from offset *)
    let to_size (o: t): size = o
    (* Size, from offset *)
    let of_size (s: size): t = s
    (* Turning an offset into an integer, if possible *)
    let to_int_opt (o: t): int option = Some o
    let to_int (o: t): int = o
    let size_to_int_opt (s: size): int option = Some s
    (* Turning an offset into an n_expr *)
    let to_n_expr (o: t): n_expr = Ne_csti o
    let size_to_n_expr (s: size): n_expr = Ne_csti s

    (** Comparisons *)
    (* Whether an offset is constant *)
    let t_is_const (_: t): bool = true
    (* Whether a size is constant *)
    let size_is_const (_: size): bool = true
    (* Compare, syntactic on AST, to build sets *)
    let compare: t -> t -> int = (-)
    (* Equality test *)
    let eq: t -> t -> bool = (=)
    let size_eq: size -> size -> bool = (=)
    (* Compare, semantic *)
    let leq (_: n_cons -> bool): t -> t -> bool = (<=)
    (* Nullness test *)
    let is_zero (o: t): bool = o = 0
    (* Semantic comparison of sizes:
     *  - returns Some i (i \in {-1,0,1}) if it can be decided
     *  - otherwise, returns None *)
    let size_order (_: n_cons -> bool) (sz0: size) (sz1: size): int option =
      Some (sz0 - sz1)
    (* Semantic comparison of sizes; attempts to prove that s0 <= s1 *)
    let size_leq (_: n_cons -> bool) (sz0: size) (sz1: size): bool =
      sz0 <= sz1
    (* Idem for offsets: search for fields in physical placement order *)
    let t_order (_: n_cons -> bool) (o0: t) (o1: t): int option =
      Some (o0 - o1)

    (** Arithmetics *)
    let add_int: t -> int -> t = (+)
    let add: t -> t -> t = (+)
    let add_size: t -> size -> t = add
    let size_add_size: size -> size -> size = (+)
    let sub: t -> t -> size = (-)
    let sub_t: t -> t -> t = (-)
    let size_sub_size: size -> size -> size = (-)
    let mul_int (o: t) (i: int): t = o * i
    (* Split an offset modulo some given stride *)
    let modulo_split (stride: int) (x: t): (t * t) (* aligned + bias *) =
      let m = x mod stride in x - m, m
    (* Checks whether is aligned on stride *)
    let is_on_stride (stride: int) (o: t): bool = o mod stride = 0

    (** Utilities *)
    (* Ids of symbolic variables *)
    let t_sym_var_ids_add (acc: IntSet.t) (_: t): IntSet.t = acc
    let size_sym_var_ids_add (acc: IntSet.t) (_: size): IntSet.t = acc

    (** Unification *)
    let t_unify (o0: t) (o1: t): ((int * int * int) list * t) option =
      if o0 = o1 then Some ([], o0)
      else None
    let size_unify (s0: size) (s1: size)
        : ((int * int * int) list * size) option =
      if s0 = s1 then Some ([ ], s0)
      else None

    (** Renaming *)
    let t_rename (_: int IntMap.t) (o: t): t = o
    let size_rename (_: int IntMap.t) (s: size): size = s
    let t_rename_opt (_: int IntMap.t) (o: t): t option = Some o
  end: OFF_SIG)

(** Implementation with string offsets:
 ** - this is currently not used;
 ** - could be used in order to analyze Java, JavaScript, Python *)
module Off_String =
  (struct
    (** None represents the null offset *)
    type t = string option
    type size = int

    (** Printing *)
    let t_2str (o: t): string =
      match o with
      | None   -> "[o:<NULL>]"
      | Some s -> Printf.sprintf "[o:%s]" s
    let size_2str: size -> string = string_of_int

    (** Constructors and conversions *)
    (* Null offset *)
    let zero: t = None
    let size_zero: int = 0
    (* Integer offset *)
    let of_int (i: int): t =
      if i = 0 then None
      else Log.fatal_exn "Off_String impl, of_int %d" i
    (* String offset *)
    let of_string (s: string): t = Some s
    (* Field (string+int) offset *)
    let of_field ((s, _): string * int): t = of_string s
    (* From a numerical domain expression *)
    let of_n_expr (e: n_expr): t =
      Log.fatal_exn "Off_String impl, of_n_expr: %s" (n_expr_2str e)
    (* Size, from an integer *)
    let size_of_int (i: int): size = i
    (* Size, from offset *)
    let to_size (o: t): size =
      if o = None then 0
      else Log.fatal_exn "Off_String impl, to_size"
    (* Size, from offset *)
    let of_size (s: size): t =
      if s = 0 then None
      else Log.fatal_exn "Off_String impl, of_size"
    (* Turning an offset into an integer, if possible *)
    let to_int_opt (o: t): int option = None
    let to_int (o: t): int = failwith "Off_string.to_int_exn"
    let size_to_int_opt (s: size): int option = Some s
    (* Turning an offset into an n_expr *)
    let to_n_expr: t -> n_expr = function
      | None -> Ne_csti 0
      | _ -> Log.fatal_exn "Off_String impl, to_n_expr"
    let size_to_n_expr (s: size): n_expr = Ne_csti s

    (** Comparisons *)
    (* Whether an offset is constant *)
    let t_is_const (_: t): bool = true
    (* Whether a size is constant *)
    let size_is_const (_: size): bool = true
    (* Compare, syntactic on AST, to build sets *)
    let compare (o0: t) (o1: t): int =
      match o0, o1 with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some s0, Some s1 -> String.compare s0 s1
    (* Equality test *)
    let eq (o0: t) (o1: t): bool = compare o0 o1 = 0
    let size_eq: size -> size -> bool = (=)
    (* Compare, semantic *)
    let leq (_: n_cons -> bool) (o0: t) (o1: t): bool =
      match o0, o1 with
      | None, _ -> true
      | Some _, None -> false
      | Some s0, Some s1 -> Log.fatal_exn "Off_string impl, leq"
    (* Nullness test *)
    let is_zero (o: t): bool = o = None
    (* Semantic comparison of sizes:
     *  - returns Some i (i \in {-1,0,1}) if it can be decided
     *  - otherwise, returns None *)
    let size_order (_: n_cons -> bool) (sz0: size) (sz1: size): int option =
      Some (sz0 - sz1)
    (* Semantic comparison of sizes; attempts to prove that s0 <= s1 *)
    let size_leq (_: n_cons -> bool) (sz0: size) (sz1: size): bool =
      sz0 <= sz1
    (* Idem for offsets: search for fields in physical placement order *)
    let t_order (_: n_cons -> bool) (o0: t) (o1: t): int option =
      None

    (** Arithmetics *)
    let add_int (o: t) (i: int): t =
      if i = 0 then o
      else Log.fatal_exn "Off_String impl, add_int"
    let add (o0: t) (o1: t): t =
      match o0, o1 with
      | None, o | o, None -> o
      | Some _, Some _ -> Log.fatal_exn "Off_String impl, add"
    let add_size (o0: t) (sz: size): t =
      if sz = 0 then o0 else Log.fatal_exn "Off_String impl, add_size"
    let size_add_size: size -> size -> size = (+)
    let sub (o0: t) (o1: t): int =
      if eq o0 o1 then 0
      else Log.fatal_exn "Off_String impl, sub" 
    let sub_t (o0: t) (o1: t): t =
      if eq o0 o1 then None
      else Log.fatal_exn "Off_String impl, sub_t"
    let size_sub_size: size -> size -> size = (-)
    let mul_int (o: t) (i: int): t =
      if i = 1 then o
      else if i = 0 then zero
      else Log.fatal_exn "Off_String impl, mul_int"
    (* Split an offset modulo some given stride *)
    let modulo_split (stride: int) (x: t): (t * t) (* aligned + bias *) =
      x, None (* modulo_split has no real meaning here: no split *)
    (* Checks whether is aligned on stride *)
    let is_on_stride (stride: int) (_: t): bool = false

    (** Utilities *)
    (* Ids of symbolic variables *)
    let t_sym_var_ids_add (acc: IntSet.t) (_: t): IntSet.t = acc
    let size_sym_var_ids_add (acc: IntSet.t) (_: size): IntSet.t = acc

    (** Unification *)
    let t_unify (o0: t) (o1: t): ((int * int * int) list * t) option =
      match o0, o1 with
      | None, None -> Some ([], None)
      | Some s0, Some s1 ->
          if String.compare s0 s1 = 0 then Some ([], o0)
          else None
      | None, Some _ | Some _, None -> None
    let size_unify (s0: size) (s1: size)
        : ((int * int * int) list * size) option =
      if s0 = s1 then Some ([ ], s0)
      else None

    (** Renaming *)
    let t_rename (_: int IntMap.t) (o: t): t = o
    let size_rename (_: int IntMap.t) (s: size): size = s
    let t_rename_opt (_: int IntMap.t) (o: t): t option = Some o
  end: OFF_SIG)
