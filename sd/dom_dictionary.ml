(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_dictionary.ml
 **       Dictionary for composite shape abstract domains
 ** Antoine Toubhans, 2014/05/11 *)
open Lib
open Data_structures

(** Error report *)
module Log =
  Logger.Make(struct let section = "d_dict__" and level = Log_level.DEBUG end)

(* Type for localisation of variables *)
type dic_side =
  | Dic_fst (* var. of the first shape component *)
  | Dic_snd (* var. of the second shape component *)

(* Pretty-printing *)
let dic_side_2str = function
  | Dic_fst -> "D1"
  | Dic_snd -> "D2"

(** Module signature for dictionary 
 ** a dictionary consists of binding local symvar to either 
 ** a symvar in D1 or a symvar in D2 *)
module type DIC =
  sig
    (** Type *)
    type t
    (* Empty environment *)
    val empty: t
    (* Pretty printing *)
    val t_2stri: string -> t -> string
    (* Sanity check *)
    val sanity_check: string -> t -> unit

    (** Dictionary managment *)
    (* add a fresh binding, takes an underlying symvar,
     * returns a local symvars *)
    val add_fresh: dic_side * int -> t -> int * t
    (* remove a binding, takes a local symvars *)
    val rem: int -> t -> t

    (** Convert symbolic variables *)
    (* from LOC to FST + SND *)
    val local2under: t -> int -> dic_side * int
    (* from FST to SEP *)
    val fst2local: t -> int -> int
    (* from SND to SEP *)
    val snd2local: t -> int -> int

    (** Iterators *)        
    val iter: (int -> (dic_side * int) -> unit) -> t -> unit
    val fold: (int -> (dic_side * int) -> 'a -> 'a) -> t -> 'a -> 'a
  end

(** A implementation based on hash functions *)
module Dic_hash =
  (struct
    (* Hash functions *)
    let s_hash (i: int): dic_side * int =
      match i mod 2 with
      | 0 -> Dic_fst, i/2
      | _ -> Dic_snd, (i-1)/2
    let s_hash1 (j1: int): int = 2 * j1
    let s_hash2 (j2: int): int = 2 * j2 + 1

    (** Types *)
    type t = IntSet.t

    (* Empty environment *)
    let empty: t = IntSet.empty

    (* Pretty printing *)
    let t_2stri (ind: string) (t: t): string =
      IntSet.fold
        (fun i s ->
          let loc, iu = s_hash i in
          Printf.sprintf "%s%s%i\t--->\t(%s, %i)\n"
            s ind i (dic_side_2str loc) iu
        ) t ""
    (* Sanity check *)
    let sanity_check (_: string) (_: t): unit = ()

    (** Environment managment *)
    (* add a fresh binding *)
    let add_fresh ((loc, i): dic_side * int) (e: t): int * t =
      match loc with
      | Dic_fst -> 
          let ilocal = s_hash1 i in
          assert (not (IntSet.mem ilocal e));
          ilocal, IntSet.add ilocal e
      | Dic_snd -> 
          let ilocal = s_hash2 i in
          assert (not (IntSet.mem ilocal e));
          ilocal, IntSet.add ilocal e
    (* remove a binding *)
    let rem: int -> t -> t = IntSet.remove

    (** Convert symbolic variables *)
    (* from SEP to FST + SND *)
    let local2under (_: t): int -> dic_side * int = s_hash
    (* from FST to SEP *)
    let fst2local (_: t): int -> int = s_hash1
    (* from SND to SEP *)
    let snd2local (_: t): int -> int = s_hash2

    (** Iterators *)
    let iter (f: int -> (dic_side * int) -> unit): t -> unit =
      IntSet.iter (fun i -> f i (s_hash i))
    let fold (f: int -> (dic_side * int) -> 'a -> 'a): t -> 'a -> 'a =
      IntSet.fold (fun i -> f i (s_hash i))
  end: DIC)

(** A implementation based on maps *)
module Dic_map =
  (struct
    (** Types *)
    type t = 
        { t_img:     (dic_side * int) IntMap.t; (* image DSep -> D1 + D2 *)
          t_rev_fst: int IntMap.t;             (* image D1 -> DSep *)
          t_rev_snd: int IntMap.t;             (* image D2 -> DSep *)
          t_nkey:    Keygen.t                  (* key allocator *) }

    (* Empty environment *)
    let empty: t = 
      { t_img     = IntMap.empty;
        t_rev_fst = IntMap.empty;
        t_rev_snd = IntMap.empty;
        t_nkey    = Keygen.empty }

    (* Pretty printing *)
    let t_2stri (ind: string) (t: t): string = 
      IntMap.fold
        (fun i (loc, iu) s -> 
          Printf.sprintf "%s%s%i\t--->\t(%s, %i)\n"
            s ind i (dic_side_2str loc) iu
        ) t.t_img ""
    (* Sanity check *)
    let sanity_check (mess: string) (x: t): unit =
      IntMap.iter
        (fun i (loc, j) ->
          match loc with
          | Dic_fst ->
              begin
                try
                  if IntMap.find j x.t_rev_fst != i then
                    Log.fatal_exn
                      "%s: incorrect mapping %i -> %s, %i"
                      mess i (dic_side_2str loc) j
                with Not_found ->
                  Log.fatal_exn
                    "%s: mapping %i -> %s, %i has no reverse"
                    mess i (dic_side_2str loc) j
              end
          | Dic_snd ->
              begin
                try
                  if IntMap.find j x.t_rev_snd != i then
                    Log.fatal_exn
                      "%s: incorrect mapping %i -> %s, %i"
                      mess i (dic_side_2str loc) j
                with Not_found ->
                  Log.fatal_exn
                    "%s: mapping %i -> %s, %i has no reverse"
                    mess i (dic_side_2str loc) j
              end
        ) x.t_img

    (** Environmemt managment *)
    (* add a fresh binding *)
    let add_fresh ((loc, i): dic_side * int) (e: t): int * t =
      match loc with
      | Dic_fst ->
          assert (not (IntMap.mem i e.t_rev_fst));
          let keys, ilocal = Keygen.gen_key e.t_nkey in
          let r = { e with
                    t_img     = IntMap.add ilocal (Dic_fst, i) e.t_img;
                    t_rev_fst = IntMap.add i ilocal e.t_rev_fst;
                    t_nkey    = keys } in
          ilocal, r
      | Dic_snd -> 
          assert (not (IntMap.mem i e.t_rev_snd));
          let keys, ilocal = Keygen.gen_key e.t_nkey in
          let r = { e with
                    t_img     = IntMap.add ilocal (Dic_snd, i) e.t_img;
                    t_rev_snd = IntMap.add i ilocal e.t_rev_snd;
                    t_nkey    = keys } in
          ilocal, r
    (* remove a binding *)
    let rem (i: int) (e: t): t =
      let rev1, rev2 = 
        match IntMap.find i e.t_img with (* this must not fail *)
        | Dic_fst, i1 -> IntMap.remove i1 e.t_rev_fst, e.t_rev_snd
        | Dic_snd, i2 -> e.t_rev_fst, IntMap.remove i2 e.t_rev_snd in
      { t_img     = IntMap.remove i e.t_img;
        t_rev_fst = rev1;
        t_rev_snd = rev2;
        t_nkey    = Keygen.release_key e.t_nkey i }

    (** Convert symbolic variables *)
    (* from SEP to FST + SND *)
    let local2under (e: t) (i: int): dic_side * int = IntMap.find i e.t_img
    (* from FST to SEP *)
    let fst2local (e: t) (i1: int): int = IntMap.find i1 e.t_rev_fst
    (* from SND to SEP *)
    let snd2local (e: t) (i2: int): int = IntMap.find i2 e.t_rev_snd

    (** Iterators *)
    let iter (f: int -> (dic_side * int) -> unit) (x: t): unit =
      IntMap.iter f x.t_img
    let fold (f: int -> (dic_side * int) -> 'a -> 'a) (x: t): 'a -> 'a =
      IntMap.fold f x.t_img
  end: DIC)

