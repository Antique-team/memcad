(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: off_impl.mli
 **       simple implementations of various forms of offsets
 ** Xavier Rival, 2012/04/23 *)
open Off_sig

(** Implementation with integer offsets:
 ** - this is the default choice *)
module Off_Int: OFF_SIG

(** Implementation with string offsets:
 ** - this is currently not used;
 ** - could be used in order to analyze Java, JavaScript, Python *)
module Off_String: OFF_SIG
