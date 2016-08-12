(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: refcount.ml
 **       A basic (persistent) reference counting structure
 ** Xavier Rival, 2016/04/11 *)
open Lib


(** Error report *)
module Log =
  Logger.Make(struct let section = "refc____" and level = Log_level.DEBUG end)


(** Structure describing reference counts *)
type 'a t = ('a, int) Aa_maps.t


(** Basic operations *)

(* Empty *)
let empty = Aa_maps.empty

(* Pp *)
let t_2stri (f: 'a -> string) (ind: string) (x: 'a t): string =
  Aa_maps.fold
    (fun k d acc -> Printf.sprintf "%s%s%s => %d\n" acc ind (f k) d) x ""

(* Reference addition/removal *)
let incr (k: 'a) (x: 'a t): 'a t =
  let o = try Aa_maps.find k x with Not_found -> 0 in
  Aa_maps.add k (o+1) x
let decr (k: 'a) (x: 'a t): 'a t * bool (* true if down to 0 *) =
  let o =
    try Aa_maps.find k x
    with Not_found -> Log.fatal_exn "rc not found" in
  if o <= 0 then Log.fatal_exn "rc not high enough"
  else if o = 1 then Aa_maps.remove k x, true
  else Aa_maps.add k (o-1) x, false

(* Check if positive reference *)
let hasref (k: 'a) (x: 'a t): bool (* true if >= 1 *) =
  try Aa_maps.find k x > 0 with Not_found -> false
