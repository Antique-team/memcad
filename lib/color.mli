(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: color.mli
 **       Logging infrastructure; log level colors
 ** Francois Berenger, 26/07/2016 *)

(* available colors *)
type t =
  | Reset
  | Bold
  | Black | Red | Green | Yellow | Blue | Magenta | Cyan | White
  | Default

(* corresponding string for an ANSI terminal *)
val to_string: t -> string
