(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: config_sig.ml
 **       configuration file signature
 ** Xavier Rival, 2011/09/29 *)

type fvalue =
  | F_int of int (* integer *)
  | F_strings of string list (* a list of plain strings *)
  | F_qstring of string (* quoted string *)

type field =
    { fname: string ;
      fval:  fvalue }

type fields = field list

(* Entry code: integer + optional revision (one character) *)
type entry_code = int * char option

(* Entry associates an entry_code to a bunch of fields *)
type entry =
    { ent_code:   entry_code; (* entry code *)
      ent_extend: entry_code option; (* extends, if any *)
      ent_fields: fields (* fields of the entry *) }

(* A file just comprises a long series of entries *)
type pconfig_file = entry list
