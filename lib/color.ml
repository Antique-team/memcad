(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: color.ml
 **       Logging infrastructure; log level colors
 ** Francois Berenger, 26/07/2016 *)

type t = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White | Default

(* ANSI terminal colors for UNIX *)
let to_string: t -> string = function
  | Black   -> "\027[30m"
  | Red     -> "\027[31m"
  | Green   -> "\027[32m"
  | Yellow  -> "\027[33m"
  | Blue    -> "\027[34m"
  | Magenta -> "\027[35m"
  | Cyan    -> "\027[36m"
  | White   -> "\027[37m"
  | Default -> "\027[39m"

let reset: string = "\027[0m"
