
(* read all lines of file 'fn' *)
let lines_of_file fn =
  BatList.of_enum (BatFile.lines_of fn)

(* store the list of strings 'lines' into file 'fn' *)
let list_to_file fn lines =
  let out = open_out fn in
  List.iter (Printf.fprintf out "%s\n") lines;
  close_out out

(* extract line numbers and exact lines that must be modified *)
let parse_lines_file fn =
  let lines = lines_of_file fn in
  List.map (fun s ->
      Scanf.sscanf s "%d %s"
        (fun d s -> (d, " " ^ s))
    ) lines

let can_compile () =
  Sys.command "(obuild build exe-analyze 2>&1) > /dev/null" = 0

let increase_arity current_line =
  let res = Str.replace_first (Str.regexp " T.app9 ") " T.app10 " current_line in
  let res = Str.replace_first (Str.regexp " T.app8 ") " T.app9 "  res in
  let res = Str.replace_first (Str.regexp " T.app7 ") " T.app8 "  res in
  let res = Str.replace_first (Str.regexp " T.app6 ") " T.app7 "  res in
  let res = Str.replace_first (Str.regexp " T.app5 ") " T.app6 "  res in
  let res = Str.replace_first (Str.regexp " T.app4 ") " T.app5 "  res in
  let res = Str.replace_first (Str.regexp " T.app3 ") " T.app4 "  res in
  let res = Str.replace_first (Str.regexp " T.app2 ") " T.app3 "  res in
  let res = Str.replace_first (Str.regexp " T.app1 ") " T.app2 "  res in
  res

(* push the T.appN arity of a given line as much as possible *)
let rec push_arity fn (line_number, line) =
  Log.info "%s:%d" fn line_number;
  let all_lines = lines_of_file fn in
  let before, after' = BatList.takedrop (line_number - 1) all_lines in
  match after' with
  | [] -> assert(false)
  | current :: after ->
    let updated_line = increase_arity current in
    let (_: int) = Sys.command (Printf.sprintf "cp %s %s.bck" fn fn) in
    list_to_file fn (before @ (updated_line :: after));
    if can_compile () then
      push_arity fn (line_number, line)
    else
      (* revert file to its last compiling state *)
      let (_: int) = Sys.command (Printf.sprintf "cp %s.bck %s" fn fn) in
      ()

let main () =
  Log.set_log_level Log.INFO;
  Log.color_on ();
  let file_to_udpate = Sys.argv.(1) in
  let lines_to_update_file = Sys.argv.(2) in
  let lines_to_update = parse_lines_file lines_to_update_file in
  List.iter
    (fun l -> push_arity file_to_udpate l)
    lines_to_update

let () = main ()
