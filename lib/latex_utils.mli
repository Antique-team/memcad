(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: latex_utils.mli
 ** utilities for LaTeX output
 ** Xavier Rival, 2012/07/17 *)

(** Latex file management *)
val open_file: string -> Unix.file_descr * out_channel

(** Header and trailer of the LaTeX files *)
val output_header: out_channel -> unit -> unit
val output_trailer: out_channel -> unit -> unit
