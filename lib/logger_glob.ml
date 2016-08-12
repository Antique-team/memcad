(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: logger_glob.ml
 **       Logging infrastructure; global HT to store log level
 **       per section/module
 ** Francois Berenger, 26/07/2016 *)

(* hash table to control at runtime log level per section *)
let section2level: (string, Log_level.t) Hashtbl.t = Hashtbl.create 71

let set_log_level (sec: string) (lvl: Log_level.t): unit =
  (* let () = Printf.printf "FBR: set_log_level %s %s\n" *)
  (*     sec (Log_level.to_string lvl) in *)
  Hashtbl.replace section2level sec lvl

let get_log_level (sec: string): Log_level.t =
  try Hashtbl.find section2level sec
  with Not_found -> Log_level.INFO (* default log level *)

(* this is where to define module groups so that changing the log level
 * for several modules at the same time is easy *)
let expand_modules_group (group: string): string list =
  match group with
  | "all" -> Hashtbl.fold (fun k _v acc -> k :: acc) section2level []
  | _ -> []
