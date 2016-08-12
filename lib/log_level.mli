(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: log_level.mli
 **       Logging infrastructure; log levels
 ** Francois Berenger, 26/07/2016 *)

(* available log levels *)
type t =
  | FORCE (* you want to force a message to be displayed *)
  | FATAL (* an unrecoverable error was encountered; will crash soon *)
  | TODO (* a todo was encountered *)
  | ERROR (* an error was encountered *)
  | WARN (* something less severe than an error was encountered *)
  | INFO (* you want to give feedback to the user *)
  | DEBUG (* you want to give feedback to the programmer *)

(* construction *)
val of_string: string -> t

(* conversions *)
val to_string: t -> string
val to_int: t -> int

(* default color mapping *)
val to_color: t -> Color.t
