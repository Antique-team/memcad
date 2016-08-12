(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: timer.ml
 **       Primitives for the extraction of timing information
 ** Xavier Rival, 2012/08/11 *)
open Data_structures
open Lib

(** Error report *)
module Log =
  Logger.Make(struct let section = "timer___" and level = Log_level.DEBUG end)

(* A timer is specified by the processor time when it was started *)
type timer = float

let cpu_timestamp () =
  let now = Unix.times () in
  Unix.(now.tms_utime  +.
        now.tms_stime  +.
        now.tms_cutime +.
        now.tms_cstime)

(** Operation on timers *)
let start (): timer = cpu_timestamp ()
let current_time (t: timer): float = cpu_timestamp () -. t

(** Clock structure
 ** - at most one active clock;
 ** - when a clock is active we still remember when it started (total time)
 ** - when a clock is active, other clocks are in suspended state *)
(* Suspended clock *)
type suspended =
    { s_id:      string * string; (* module, name of the clock *)
      s_start:   float; (* time at which the clock started first *)
      s_running: float; (* time elapsed under that clock, so far *) }
(* System of clocks *)
type clock =
    { c_id:      string * string; (* module, name of the current clock *)
      c_start:   float; (* time at which the current clock started first *)
      c_running: float; (* time elapsed under the current clock, so far *)
      c_restart: float; (* time at which the current clock restarted last *)
      c_susp:    suspended list;  (* list of suspended clocks *) }
(* The clock:
 *  - None when no clock is active (no suspended clock)
 *  - Some when a clock is active / some are suspended *)
let clock: clock option ref = ref None
(* Starting a new clock as the current clock
 *  (turns the previously active clock into suspended mode) *)
let clock_start (m: string) (f: string): unit =
  let t0 = cpu_timestamp () in
  let l =
    match !clock with
    | None -> (* no clock active, create one *)
        [ ]
    | Some c ->
        let t_elapsed = t0 -. c.c_restart +. c.c_running in
        { s_id      = c.c_id;
          s_start   = c.c_start;
          s_running = t_elapsed } :: c.c_susp in
  clock := Some { c_id      = m, f;
                  c_start   = t0;
                  c_running = 0.;
                  c_restart = t0;
                  c_susp    = l }
(* Stops the current clock, check its id and returns running and total times
 *  (turns the last previously suspended clock into running mode again) *)
let clock_stop (m: string) (f: string): float * float =
  let t0 = cpu_timestamp () in
  match !clock with
  | None -> Log.fatal_exn "there is no clock to stop"
  | Some c ->
      if String.compare m (fst c.c_id) != 0 then
        Log.fatal_exn "wrong module: %s-%s [%d]"
          m (fst c.c_id) (List.length c.c_susp);
      if String.compare f (snd c.c_id) != 0 then
        Log.fatal_exn "wrong function";
      let t_total  = t0 -. c.c_start
      and t_active = t0 -. c.c_restart +. c.c_running in
      begin
        match c.c_susp with
        | [ ] -> clock := None
        | c0 :: c1 ->
            clock := Some { c_id      = c0.s_id;
                            c_start   = c0.s_start;
                            c_running = c0.s_running;
                            c_restart = t0;
                            c_susp    = c1 }
      end;
      t_total, t_active

(** Time logging structure *)
(* To monitor the total time spent in some functions / modules
 *  nb: that includes time spent in sub-calls *)
type timing = { t_total:  float; (* includes sub-calls *)
                t_active: float; (* only time in self *) }
type timing_data = timing list StringMap.t
(* The database for timing *)
let time_funs: timing_data ref = ref StringMap.empty (* functions *)
let time_mods: timing_data ref = ref StringMap.empty (* modules *)
(* Initialization *)
let init (): unit =
  time_funs := StringMap.empty;
  time_mods := StringMap.empty
(* Statistics of a function *)
let retrieve_function (s: string): timing list =
  try StringMap.find s !time_funs with Not_found -> []
(* Records the time spent in a function *)
let register_timing (fname: string) (t: timing): unit =
  let cur_rec = retrieve_function fname in
  time_funs := StringMap.add fname (t :: cur_rec) !time_funs
(* Turns a list into a total time *)
let list_to_time: timing list -> timing =
  let add t0 t1 =
    { t_total  = t0.t_total  +. t1.t_total ;
      t_active = t0.t_active +. t1.t_active } in
  List.fold_left add { t_total = 0. ; t_active = 0. }

(** Printer: time spent in all functions *)
let print_timing_infos (): unit =
  if !Flags.flag_pp_timing then
    begin
      show_sep ();
      Log.info "Timing report per module:\n";
      let l =
        StringMap.fold (fun s _ a -> max (String.length s) a) !time_mods 10 in
      let tabl = 5 + if l > 25 then 25 else l in
      StringMap.iter
        (fun s l ->
          let t = list_to_time l in
          Log.info " %s%.6f s,  %.6f s"
            (str_lflush tabl s) t.t_total t.t_active
        ) !time_mods;
      Log.info "\nTiming report per function:\n";
      let l =
        StringMap.fold (fun s _ a -> max (String.length s) a) !time_funs 10 in
      let tabl = 5 + if l > 25 then max 25 (l-4) else l in
      StringMap.iter
        (fun s l ->
          let ll = List.length l in
          let t = list_to_time l in
          Log.info " %s:%s call%s, time %.6f s,  %.6f s"
            (str_lflush tabl s)
            (str_rflush 6 (string_of_int ll)) (if ll > 1 then "s" else " ")
            t.t_total t.t_active
        ) !time_funs
    end

(** Logging module *)
module type TIMER_DEF =
  sig
    val name: string
  end
module Timer_Mod = functor (Mod: TIMER_DEF) ->
  struct
    (* Add a log entry for a function *)
    let log (f: string) (total: float) (active: float): unit =
      let timing = { t_total  = total;
                     t_active = active } in
      let update s t b =
        let o = try StringMap.find s !b with Not_found -> [ ] in
        b := StringMap.add s (t :: o) !b in
      update (Printf.sprintf "%s.%s" Mod.name f) timing time_funs;
      update Mod.name timing time_mods
    type 'a result =
      | R_res of 'a
      | R_exn of exn
    let follow = function
      | R_res r -> r
      | R_exn e -> raise e
    let start = clock_start Mod.name
    let stop  = clock_stop  Mod.name
    (* Functions computing a time *)
    let app1 s f x0 =
      start s;
      let res = try R_res (f x0) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app2 s f x0 x1 =
      start s;
      let res = try R_res (f x0 x1) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app3 s f x0 x1 x2 =
      start s;
      let res = try R_res (f x0 x1 x2) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app4 s f x0 x1 x2 x3 =
      start s;
      let res = try R_res (f x0 x1 x2 x3) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app5 s f x0 x1 x2 x3 x4 =
      start s;
      let res = try R_res (f x0 x1 x2 x3 x4) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app6 s f x0 x1 x2 x3 x4 x5 =
      start s;
      let res = try R_res (f x0 x1 x2 x3 x4 x5) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app7 s f x0 x1 x2 x3 x4 x5 x6 =
      start s;
      let res = try R_res (f x0 x1 x2 x3 x4 x5 x6) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app8 s f x0 x1 x2 x3 x4 x5 x6 x7 =
      start s;
      let res = try R_res (f x0 x1 x2 x3 x4 x5 x6 x7) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app9 s f x0 x1 x2 x3 x4 x5 x6 x7 x8 =
      start s;
      let res = try R_res (f x0 x1 x2 x3 x4 x5 x6 x7 x8) with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
    let app10 s f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      start s;
      let res =
        try R_res (f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
        with e -> R_exn e in
      let tt, ta = stop s in
      log s tt ta;
      follow res
  end
