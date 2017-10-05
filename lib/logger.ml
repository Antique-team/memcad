(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: logger.ml
 **       logging infrastructure
 ** Francois Berenger, 19/07/2016 *)

open Printf

module LL = Log_level

(* localtime is used to date events, _not_ GMT, BEWARE SCIENTIST *)

(* defaults *)
let output         = ref stdout
let level_to_color = ref LL.to_color
let use_color      = ref false
let prefix         = ref ""
let section        = ref "undef"

let set_section s =
  section := s

let get_log_level () =
  Logger_glob.get_log_level !section

let set_output o =
  output := o

let set_prefix p =
  prefix := p

let clear_prefix () =
  prefix := ""

let set_color_mapping f =
  level_to_color := f

let color_on () =
  use_color := true

let color_off () =
  use_color := false

let reset_color = Color.to_string Color.Reset

let level_to_string lvl =
  let s = LL.to_string lvl in
  if !use_color then
    let color = !level_to_color lvl in
    (Color.to_string color) ^ s ^ reset_color
  else
    s

module type S = sig
  val log   : Log_level.t -> ('a, Buffer.t, unit) format -> 'a
  val force : ('a, Buffer.t, unit) format -> 'a
  val fatal : ('a, Buffer.t, unit) format -> 'a
  val fatal_exn : ('a, Buffer.t, unit, 'b) format4 -> 'a
  val todo  : ('a, Buffer.t, unit) format -> 'a
  val todo_exn : ('a, Buffer.t, unit, 'b) format4 -> 'a
  val error : ('a, Buffer.t, unit) format -> 'a
  val warn  : ('a, Buffer.t, unit) format -> 'a
  val info  : ('a, Buffer.t, unit) format -> 'a
  val debug : ('a, Buffer.t, unit) format -> 'a
end

module type SECTION = sig
  val section: string
  val level: Log_level.t
end

module Make (S: SECTION) = struct

  (* Right after module creation: the given section has the given log level.
   * This can be changed afterwards (during command line options parsing)
   * via calls to Global.set_log_level *)
  let () =
    set_section S.section;
    Logger_glob.set_log_level S.section S.level

  let std_timestamp_str lvl =
    let ts = Unix.gettimeofday() in
    let tm = Unix.localtime ts in
    let us, _s = modf ts in
    (* example: "2012-01-13 18:26:52.091" *)
    sprintf "%04d-%02d-%02d %02d:%02d:%02d.%03d %s %s %s: "
      (1900 + tm.Unix.tm_year)
      (1    + tm.Unix.tm_mon)
      tm.Unix.tm_mday
      tm.Unix.tm_hour
      tm.Unix.tm_min
      tm.Unix.tm_sec
      (int_of_float (1_000. *. us))
      S.section
      (level_to_string lvl)
      !prefix

  (* example for a shorter timestamp string *)
  let short_timestamp_str lvl =
    sprintf "%.3f %s: " (Unix.gettimeofday()) (level_to_string lvl)

  let micro_timestamp_str lvl =
    sprintf "%s/%s: " S.section (level_to_string lvl)

  let newline = Str.regexp "\n"

  (* repeat log prefix in front of all lines *)
  let edit_multines_log prfx buff =
    let contents = Buffer.contents buff in
    let sep = "\n" ^ prfx in
    let res = Str.global_replace newline sep contents in
    Printf.fprintf !output "%s\n%!" res

  let empty_buff = Buffer.create 0

  let log lvl fmt =
    if LL.to_int lvl >= LL.to_int (get_log_level()) then
      let prfx = micro_timestamp_str lvl in
      let buff = Buffer.create 80 in
      Buffer.add_string buff prfx;
      kbprintf (edit_multines_log prfx) buff fmt
    else
      kbprintf ignore empty_buff fmt

  let log_exn lvl fmt =
    if LL.to_int lvl >= LL.to_int (get_log_level()) then
      let prfx = micro_timestamp_str lvl in
      let buff = Buffer.create 80 in
      Buffer.add_string buff prfx;
      kbprintf (fun b -> edit_multines_log prfx b; failwith "") buff fmt
    else
      kbprintf (fun _ -> failwith "") empty_buff fmt

  let force fmt = log LL.FORCE fmt
  let fatal fmt = log LL.FATAL fmt
  let fatal_exn fmt = log_exn LL.FATAL fmt
  let todo fmt = log LL.TODO fmt
  let todo_exn fmt = log_exn LL.TODO fmt
  let error fmt = log LL.ERROR fmt
  let warn  fmt = log LL.WARN  fmt
  let info  fmt = log LL.INFO  fmt
  let debug fmt = log LL.DEBUG fmt

end

include Make (struct
    let section = ""
    let width = 0
    let level = LL.INFO
  end)
