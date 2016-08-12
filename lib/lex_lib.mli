(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: lex_lib.mli
 **       lexing library functions
 ** Xavier Rival, 2011/10/15 *)

(** Support for lexing *)
(* Line numbers in lexers *)
val num_line: int ref
