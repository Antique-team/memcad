(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: off_linexpr.mli
 **       simple implementations of various forms of offsets
 ** Xavier Rival, 2012/04/23 *)
open Off_sig

(** Implementation with linear expressions over node ids
 ** - maybe extend with arbitrary symbols
 ** - this should become the default choice *)
module Off_Linexpr: OFF_SIG
