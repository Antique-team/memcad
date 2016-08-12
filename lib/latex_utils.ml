(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: latex_utils.ml
 **       utilities for LaTeX output
 ** Xavier Rival, 2012/07/17 *)
open Flags

(** Latex file management *)
let open_file (trailer: string): Unix.file_descr * out_channel =
  let cdir = Filename.dirname !analyzed_file
  and cfile = Filename.basename !analyzed_file in
  let filename = Printf.sprintf "%s/log-%s-%s.tex" cdir cfile trailer in
  let file =
    Unix.openfile filename
      [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  let chan = Unix.out_channel_of_descr file in
  file, chan

(** Header and trailer of the LaTeX files *)
let output_header (chan: out_channel) (): unit =
  Printf.fprintf chan "\\input{preamble-fg.tex}\n";
  Printf.fprintf chan "\\begin{document}\n";
  Printf.fprintf chan "\\scriptsize\n";
  Printf.fprintf chan "\\begin{pspicture}(-0.25,-2)(10,10)\n"
let output_trailer (chan: out_channel) (): unit =
  Printf.fprintf chan "\\end{pspicture}\n";
  Printf.fprintf chan "\\end{document}}\n"
