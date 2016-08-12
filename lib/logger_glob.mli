(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: logger_glob.mli
 **       Logging infrastructure
 ** Francois Berenger, 26/07/2016 *)

(* set allowed log level for given section/module *)
val set_log_level: string -> Log_level.t -> unit

(* get log level for given section *)
val get_log_level: string -> Log_level.t

(* turn a group name into a list of module names *)
val expand_modules_group: string -> string list
