(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: log_level.ml
 **       Logging infrastructure; log levels
 ** Francois Berenger, 26/07/2016 *)

type t =
  | FORCE
  | FATAL
  | TODO
  | ERROR
  | WARN
  | INFO
  | DEBUG

let of_string: string -> t = function
  | "FORCE" | "force" | "r" -> FORCE
  | "FATAL" | "fatal" | "f" -> FATAL
  | "TODO"  | "todo"  | "t" -> TODO
  | "ERROR" | "error" | "e" -> ERROR
  | "WARN"  | "warn"  | "w" -> WARN
  | "INFO"  | "info"  | "i" -> INFO
  | "DEBUG" | "debug" | "d" -> DEBUG
  | str -> failwith ("no such log level: " ^ str)

let to_string: t -> string = function
  | FORCE -> "force"
  | FATAL -> "fatal"
  | TODO  -> "todo_"
  | ERROR -> "error"
  | WARN  -> "warn_"
  | INFO  -> "info_"
  | DEBUG -> "debug"

let to_int: t -> int = function
  | FORCE -> 6
  | FATAL -> 5
  | TODO  -> 4
  | ERROR -> 3
  | WARN  -> 2
  | INFO  -> 1
  | DEBUG -> 0

(* default color mapping *)
let to_color: t -> Color.t = function
  | FORCE -> Color.Magenta
  | FATAL -> Color.Magenta
  | TODO  -> Color.Magenta
  | ERROR -> Color.Red
  | WARN  -> Color.Yellow
  | INFO  -> Color.Green
  | DEBUG -> Color.Cyan
