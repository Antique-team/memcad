(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: keygen.ml
 **       generation of keys in [0,n]
 ** Xavier Rival, 2013/05/16 *)
open Data_structures
open Lib

module Log =
  Logger.Make(struct let section = "keygen__" and level = Log_level.DEBUG end)


(** Structure to keep free keys *)
(* The next key is:
 * either t_n if t_s is empty
 * or     the minimal elemnt of t_s otherwise *)
type t =
    { t_n: int;
      t_s: IntSet.t; }

(** Functions over t *)
(* Sanity check *)
let internal_sanity_check (loc: string) (x: t): unit =
  if x.t_n < 0 then
    Log.fatal_exn "internal_sanity_check_failed <%s>: max" loc;
  IntSet.iter
    (fun i ->
       if i < 0 then
         Log.fatal_exn
           "internal_sanity_check_failed <%s>: neg index: %d" loc i;
       if i >= x.t_n - 1 then
         Log.fatal_exn
           "internal_sanity_check_failed <%s>: over max index: %d" loc i;
    ) x.t_s
let sanity_check (loc: string) (elts: IntSet.t) (x: t): unit =
  let name = Printf.sprintf "sanity-check (%s)" loc in
  if x.t_n < 0 then Log.fatal_exn "%s; top bound negative" name;
  for i = 0 to x.t_n - 1 do
    match IntSet.mem i elts, IntSet.mem i x.t_s with
    | false, true | true, false -> ()
    | true, true ->
        Log.fatal_exn "%s; %d allocated AND free" name i
    | false, false ->
        Log.fatal_exn "%s; %d NEITHER allocated NOR free" name i
  done;
  if IntSet.cardinal elts + IntSet.cardinal x.t_s != x.t_n then
    Log.fatal_exn "%s; cardinality issue" name
(* Empty *)
let empty: t = { t_n = 0;
                 t_s = IntSet.empty }
(* Pretty-printing *)
let t_2str (x: t): string =
  Printf.sprintf "[|%d | {%s}|]" x.t_n (IntSet.t_2str ";" x.t_s)
(* Generate a new key *)
let gen_key (x: t): t * int =
  assert (x.t_n < max_int);
  if x.t_s = IntSet.empty then
    { x with t_n = x.t_n + 1 }, x.t_n
  else
    let n = IntSet.min_elt x.t_s in
    { x with t_s = IntSet.remove n x.t_s }, n
(* Use a key *)
let use_key (x: t) (k: int): t =
  assert (k >= 0);
  if k = x.t_n then
    { x with t_n = x.t_n + 1 }
  else if k < x.t_n then
    begin
      if IntSet.mem k x.t_s then
        { x with t_s = IntSet.remove k x.t_s }
      else Log.fatal_exn "keygen,use_key: %d" k
    end
  else
    let rec aux i acc =
      if i < x.t_n then acc
      else aux (i-1) { acc with t_s = IntSet.add i acc.t_s } in
    aux (k-1) { x with t_n = k+1 }
(* Is a key used *)
let key_is_used (x: t) (k: int): bool =
  k < x.t_n && not (IntSet.mem k x.t_s)
(* Release a key *)
let release_key (x: t) (i: int): t =
  if Flags.flag_debug_keygen then
    begin
      Log.force "release %d in %s" i (t_2str x);
      internal_sanity_check "release,before" x
    end;
  assert (i >= 0);
  assert (i < x.t_n);
  let rec fix_last (x: t): t =
    let c = x.t_n - 1 in
    if IntSet.mem c x.t_s then
      begin
        fix_last { t_n = x.t_n - 1;
                   t_s = IntSet.remove c x.t_s }
      end
    else x in
  let x =
    if i = x.t_n - 1 then
      fix_last { x with t_n = x.t_n - 1 }
    else
      { x with t_s = IntSet.add i x.t_s } in
  if Flags.flag_debug_keygen then
    begin
      internal_sanity_check "release,after" x;
      Log.force "release result: %s" (t_2str x)
    end;
  x
        
(* Get all nodes (for debug) *)
let get_nodes (x: t): IntSet.t =
  let r = ref IntSet.empty in
  for i = 0 to x.t_n - 1 do
    if not (IntSet.mem i x.t_s) then r := IntSet.add i !r
  done;
  !r
(* Equality test (expensive) *)
let equal (x: t) (y: t): bool =
  x == y || (x.t_n = y.t_n && IntSet.equal x.t_s y.t_s)
