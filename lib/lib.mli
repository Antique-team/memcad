(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: lib.mli
 **       library functions
 ** Xavier Rival, 2011/05/19 *)
open Data_structures

(** Logging of assertion results *)
val log_assert: bool -> unit

(** Export support *)
val show_sep: unit -> unit

(** Exit after displaying a status message, including warnings *)
val show_end_status_report: float -> unit
val pipe_end_status_report: unit  -> unit

(** Exceptions to stop computations *)
exception Stop
exception True
exception False


(** Support for parsing *)
(* Generic parsing function *)
val read_from_file:
    string -> ((Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'a)
      -> (Lexing.lexbuf -> 'b) -> string -> 'a
val read_from_string:
    string -> ((Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'a)
      -> (Lexing.lexbuf -> 'b) -> string -> 'a

(** String operations *)
(* Generate series of spaces *)
val mk_space: int -> string
(* Flush left and right, up to a given length *)
val str_lflush: int -> string -> string
val str_rflush: int -> string -> string
(* Length of string representation *)
val posint_len: int -> int

(** Support for pretty-printing *)
(* printing a list of integers *)
val intlist_2str: int list -> string
(* printing of a list with separators *)
val gen_list_2str: string -> ('a -> string) -> string -> 'a list -> string
(* printing a set of integers *)
val intset_2str: IntSet.t -> string
(* printing a set of pairs of integers *)
val pairset_2str: PairSet.t -> string

(** IO *)
val with_in_file: string -> (in_channel -> 'a) -> 'a
val with_out_file: string -> (out_channel -> 'a) -> 'a
val get_line: string -> int -> string

(** System *)
val run_command: string -> Unix.process_status
