(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_process.mli
 **       processing stages for the "small-C" frontend
 ** Xavier Rival, 2013/07/07 *)
open C_sig

(** Binding variables to unique IDs *)
val max_c_var_id: int ref
val bind_c_prog: c_prog -> c_prog

(** Processing of a parsed abstract syntax tree *)
(* 1. fix types;
 * 2. elaborate types;
 * 3. fix types again;
 * 4. binding of unique IDs;
 * 5. typing the program
 * 6. type elaboration
 * 7. syntactic post-treatment (unroll commands) *)
val process_c_prog: c_prog -> c_prog
