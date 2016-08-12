(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: quickr_dump.ml
 **       Dumping the activity of the set domain
 ** Xavier Rival, 2015/05/27 *)
open Data_structures
open Lib
open Offs

open Nd_sig
open Set_sig
open Svenv_sig

(** QUICr internal names *)
module L = SETr.SymSing.Logic
module R = SETr.Rename

(** Error handling *)
module Log =
  Logger.Make(struct let section = "nd_quicd" and level = Log_level.DEBUG end)

(** Logging facility *)
let opt_chan: out_channel option ref = ref None
let log_open ( ): out_channel =
  let filename = Printf.sprintf "%s.strace" !Flags.filebase in
  let file =
    Unix.openfile filename
      [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  let chan = Unix.out_channel_of_descr file in
  opt_chan := Some chan;
  chan
let log_str (str: string): unit =
  let chan =
    match !opt_chan with
    | None -> log_open ( )
    | Some chan -> chan in
  Printf.fprintf chan "%s" str

let pp_list sep pp =
  let rec aux l =
    match l with
    | [ ] -> ""
    | [ a ] -> pp a
    | a :: b -> Printf.sprintf "%s%s%s" (pp a) sep (aux b) in
  aux

let rec out_expr = function
  | L.Empty -> "{ }"
  | L.Var i -> string_of_int i
  | L.Sing i -> Printf.sprintf "{ %d }" i
  | L.DisjUnion (e0, e1) ->
      Printf.sprintf "%s U+ %s" (out_expr e0) (out_expr e1)
  | _ -> Log.fatal_exn "out_expr: unsupported expression"
let out_cnstr = function
  | L.SubEq (e0, e1) -> Printf.sprintf "%s <= %s" (out_expr e0) (out_expr e1)
  | L.Eq (e0, e1) -> Printf.sprintf "%s = %s" (out_expr e0) (out_expr e1)
  | L.In (i, e) -> Printf.sprintf "%d in %s" i (out_expr e)
  | _ -> Log.fatal_exn "out_cnstr: unsupported constraint"

(** Abstract domain functor *)

(* This functor attempts to dump a log of the operations performed
 * in the set domain:
 *  - it gives an ID to each set abstract value generated
 *  - it produces an ML program doing the same operations
 *    assuming set abstract values are represented in a module D
 *)
module Make = functor (D: SETr.Domain
                      with type ctx   = unit
                      and  type sym   = int
                      and  type cnstr = int L.t) ->
  (struct
    (** Basic types *)
    type ctx = unit
    type sym = int
    type cnstr = int L.t
    type output = D.output
    type query = D.query

    (** Type of abstract values *)
    type t =
        { t_idx:  int; (* the index of the abstract value *)
          t_u:    D.t; (* the real abstract value *) }

    (** Indexing *)
    (* Default: x(0) is bot; x(1) is top *)
    let indexer: Keygen.t ref = ref Keygen.empty
    let make str u =
      let kg, idx = Keygen.gen_key !indexer in
      log_str (Printf.sprintf "let x%d = %s\n" idx str);
      indexer := kg;
      { t_idx = idx;
        t_u   = u }

    (** [init ()] creates a new context *)
    let init = D.init

    (** Basic lattice functions *)
    (* Bottom element (empty context) *)
    let bottom ( ): t = make "bottom" (D.bottom ( ))
    let is_bottom () (x: t): bool =
      D.is_bottom () x.t_u
    (* Top element (empty context) *)
    let top ( ): t = make "top" (D.top ( ))
    let is_top () x =
      log_str (Printf.sprintf "is_top x%d\n" x.t_idx);
      D.is_top () x.t_u
    (* Pretty-printing, with indentation *)
    let pp_debug () pp ch x = D.pp_debug () pp ch x.t_u
    let pp_print () pp ch x = D.pp_print () pp ch x.t_u


    (** Management of symbolic variables *)
    let context _ = ( )
    (* [symbols t] returns the symbols constrained in [t] *)
    let symbols () (x: t) =
      D.symbols () x.t_u

    (** Comparison and join operators *)
    (* Comparison *)
    let le () (x0: t) (x1: t): bool =
      let b = D.le () x0.t_u x1.t_u in
      log_str (Printf.sprintf
                 "le x%d x%d\n"
                 x0.t_idx x1.t_idx);
      b
    (* Widening *)
    let widening () (x0: t) (x1: t): t =
      let str = Printf.sprintf "widening x%d x%d" x0.t_idx x1.t_idx in
      make str (D.widening () x0.t_u x1.t_u)
    (* Join *)
    let join () (x0: t) (x1: t): t =
      let str = Printf.sprintf "join x%d x%d" x0.t_idx x1.t_idx in
      make str (D.join () x0.t_u x1.t_u)
    (* Meet *)
    let meet () (x0: t) (x1: t): t =
      let str = Printf.sprintf "meet x%d x%d" x0.t_idx x1.t_idx in
      make str (D.meet () x0.t_u x1.t_u)

    (** Set satisfiability *)
    let sat () (x: t) (c: cnstr): bool =
      let b = D.sat () x.t_u c in
      log_str (Printf.sprintf "sat x%d %s\n" x.t_idx (out_cnstr c));
      b

    (** Set condition test *)
    let constrain () (sc: cnstr) (x: t): t =
      let str = Printf.sprintf "constrain %s x%d" (out_cnstr sc) x.t_idx in
      make str (D.constrain () sc x.t_u)

    (** Forget (if the meaning of the sv changes) *)
    let forget () (l: int list) (x: t): t =
      if l = [ ] then x
      else
        let str =
          Printf.sprintf "forget %s x%d" (pp_list " " string_of_int l) x.t_idx in
        make str (D.forget () l x.t_u)

    (** Renaming (e.g., post join) *)
    let rename_symbols () (r: sym R.t) (x: t): t =
      let l = R.fold (fun i j l -> (i, j) :: l) r [ ] in
      let lstr =
        let pp (i, j) = Printf.sprintf "%d -> %d" i j in
        pp_list "; " pp l in
      let str = Printf.sprintf "rename [ %s ] x%d" lstr x.t_idx in
      make str (D.rename_symbols () r x.t_u)

    (** Additional functions, not used for now *)
    let combine () q x = make "combine" (D.combine () q x.t_u)
    let query () x = D.query () x.t_u
    let serialize () x = D.serialize () x.t_u
  end: SETr.Domain
  with type ctx   = unit
  and  type sym   = int
  and  type cnstr = int L.t)
