(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: lib.ml
 **       library functions
 ** Xavier Rival, 2011/05/19 *)
open Data_structures
open Flags


(** Error report (for module lib) *)
module Log =
  Logger.Make(struct let section = "lib_____" and level = Log_level.DEBUG end)


(** Counters *)
let count_assert_ok: int ref = ref 0
let count_assert_ko: int ref = ref 0

(** Export support *)
let show_sep (): unit =
  Log.info
    "\n\n=======================================================\n"

(** Logging of assertion results *)
let log_assert (b: bool): unit =
  if flag_log_assert then
    incr (if b then count_assert_ok else count_assert_ko)


(** Exit after displaying a status message, including warnings *)
let show_end_status_report (time_spent: float): unit =
  show_sep ();
  if !flag_pp_timing then
    Log.info "Final status report (%.4f sec spent)" time_spent;
  if flag_log_assert then
    begin
      Log.info "- assertions proved:\t %d (context)" !count_assert_ok;
      Log.info "- assertions not proved: %d (context)"  !count_assert_ko;
      exit !count_assert_ko
    end
let pipe_end_status_report ( ): unit =
  Log.info "Called writing procedure!";
  if !use_pipe then
    let file =
      if flag_debug_open_file then
        Log.force "About to open (pipe for report): %s" pipe_name;
      Unix.openfile pipe_name
        [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
    let chan = Unix.out_channel_of_descr file in
    Log.info "Writing results over pipe %s..." pipe_name;
    Printf.fprintf chan "%d\n%d\n" !count_assert_ok !count_assert_ko;
    Log.info "Results written over the pipe!";
    flush chan;
    Unix.close file


(** Exceptions to stop computations *)
exception Stop
exception True
exception False


(** Support for parsing *)

(* Generic parsing function *)
let read_from_lexbuf
    (kind: string)
    (loc: string)
    (f_parse: (Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'a)
    (f_lexe: Lexing.lexbuf -> 'b)
    (lexbuf: Lexing.lexbuf): 'a =
  Lex_lib.num_line := 1;
  try f_parse f_lexe lexbuf
  with
  | e ->
    Log.fatal_exn "Error during %s parsing, at line %d in %s: %s\n"
      kind !Lex_lib.num_line loc (Printexc.to_string e)

(* Generic "from file" parsing function *)
let read_from_file
    (kind: string)
    (f_parse: (Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'a)
    (f_lexe: Lexing.lexbuf -> 'b)
    (filename: string): 'a =
  if flag_debug_open_file then
    Log.force "About to open (gen: %s): %s" kind filename;
  let file = Unix.openfile filename [ Unix.O_RDONLY ] 0o644 in
  let channel = Unix.in_channel_of_descr file in
  let lexbuf = Lexing.from_channel channel in
  read_from_lexbuf kind (Printf.sprintf "file %s" filename)
    f_parse f_lexe lexbuf

(* Generic "from string" parsing function *)
let read_from_string
    (kind: string)
    (f_parse: (Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'a)
    (f_lexe: Lexing.lexbuf -> 'b)
    (s: string): 'a =
  read_from_lexbuf kind "string" f_parse f_lexe (Lexing.from_string s)


(** String operations *)
(* Generate series of spaces *)
let mk_space (i: int) = String.make i ' '
(* Flush left and right, up to a given length *)
let str_lflush (len: int) (str: string): string =
  let l = String.length str in
  if l > len then Log.fatal_exn "lflush"
  else Printf.sprintf "%s%s" str (mk_space (len - l))
let str_rflush (len: int) (str: string): string =
  let l = String.length str in
  if l > len then Log.fatal_exn "rflush"
  else Printf.sprintf "%s%s" (mk_space (len - l)) str
(* Length of string representation *)
let rec posint_len (i: int): int =
  if i < 0 then Log.fatal_exn "posing_len applied to negative"
  else if i < 10 then 1
  else 1 + posint_len (i / 10)


(** Support for pretty-printing *)
(* printing of a list with separators *)
let gen_list_2str
    (empty: string) (f: 'a -> string) (sep: string) (l: 'a list): string =
  match l with
  | [ ] -> empty
  | [ a ] -> f a
  | a :: ll ->
      List.fold_left
        (fun acc x -> Printf.sprintf "%s%s%s" acc sep (f x)) (f a) ll
(* printing a list of integers *)
let intlist_2str (l: int list): string =
  "[" ^ (gen_list_2str "" string_of_int ";" l) ^ "]"
(* printing a set of integers *)
let intset_2str (s: IntSet.t): string =
  Printf.sprintf "{ %s }" (IntSet.t_2str "; " s)
(* printing a set of pairs of integers *)
let pairset_2str (s: PairSet.t): string =
  Printf.sprintf "{ %s }" (PairSet.t_2str "; " s)


(** IO *)
let with_in_file (fn: string) (f: in_channel -> 'a): 'a =
  let input = open_in fn in
  let res = f input in
  close_in input;
  res
let with_out_file (fn: string) (f: out_channel -> 'a): 'a =
  let output = open_out fn in
  let res = f output in
  close_out output;
  res
(* retrieve line number 'n' from file named 'fn'
 * n.b. the first line is number 1 (as in text editors) *)
let get_line (fn: string) (n: int): string =
  if n <= 0 then failwith "lib.ml: get_line: n <= 0";
  let rec loop input i =
    if i = 1 then
      input_line input
    else
      let (_: string) = input_line input in
      loop input (i - 1) in
  with_in_file fn (fun input -> loop input n)


(** System *)
let run_command (cmd: string): Unix.process_status =
  Log.info "running: %s" cmd;
  Unix.system cmd
