(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: sv_sig.ml
 **       signatures of the symbolic variables description
 ** Xavier Rival, 2014/12/29 *)


(** Component used to describe SV types *)
type ntyp =
  | Ntaddr  (* address *)
  | Ntint   (* integer value *)
  | Ntraw   (* raw series of bits, may be e.g., array space *)
  | Ntset   (* set parameter (maybe change type) *)


(** A symbolic variable is a pair:
 **  - module ID: index + name of the module that created the symvar
 **  - symvar ID: index of the symvar in that module *)
type mod_id = int * string
type sv_id =
    { sv_mod: mod_id;
      sv_sv:  int }
