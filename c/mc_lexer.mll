(** MemCAD analyzer
 **
 ** c_lexer.mll
 ** MemCAD commands lexer
 ** Xavier Rival, 2011/12/26 *)
{
open Mc_parser
(* Extraction of the size out of an arrow *)
let extract_size_arrow (s: string): int =
  let n = String.length s in
  assert (n > 3);
  int_of_string (String.sub s 1 (n-3))
(* String tokens hash *)
let hash_string_tokens = Hashtbl.create 10
let hash_setstring_tokens = Hashtbl.create 3
let _ =
  let lst_string_tokens =
    [ "add_inductive",    T_add_inductive;
      "add_segment",      T_add_segment;
      "check_segment",    T_check_segment;
      "check_bottomness", T_check_bottomness;
      "check_inductive",  T_check_inductive;
      "decl_setvars",     T_decl_setvars;
      "force_live",       T_force_live;
      "kill_flow",        T_kill_flow;
      "merge",            T_merge;
      "output_dot",       T_output_dot;
      "output_stdout",    T_output_stdout;
      "reduce_eager",     T_reduce_eager;
      "reduce_localize",  T_reduce_localize;
      "sel_merge",        T_sel_merge;
      "set_assume",       T_add_setexprs;
      "assume",           T_assume;
      "set_check",        T_check_setexprs;
      "unfold",           T_unfold;
      "unfold_bseg",      T_unfold_bseg;
      "unroll",           T_unroll;
      (* booleans *)
      "false",            V_bool false;
      "true",             V_bool true;
      (* Minix stuffs, temporary *)
      "array_check",      T_array_check;
      "array_assume",     T_array_assume;
    ] in
  List.iter (fun (str, tok) -> Hashtbl.add hash_string_tokens str tok)
    lst_string_tokens
let _ =
  let lst_setstring_tokens =
    [ "$empty",            T_setempty;
      "$in",               T_setin;
      "$sub",              T_subseteq;
      "$euplus",           T_euplus;
    ] in
  List.iter (fun (str, tok) -> Hashtbl.add hash_setstring_tokens str tok)
    lst_setstring_tokens
let retrieve_string_tok (s: string) =
  try Hashtbl.find hash_string_tokens s
  with Not_found -> V_string s
let retrieve_setstring_tok (s: string) =
  try Hashtbl.find hash_setstring_tokens s
  with Not_found -> failwith ("unbound lexeme in MemCAD string: " ^ s)
}

rule token = parse
| ' ' | '\t'              { token lexbuf }
| '\n'                    { incr Lex_lib.num_line; token lexbuf }
| '%'[^'\n']*'\n'   (* comment lines *)
                          { incr Lex_lib.num_line; token lexbuf }
| '-'['0'-'9']+'-''>'     { let str = Lexing.lexeme lexbuf in
                            V_size_arrow (extract_size_arrow str) }
| ['0'-'9']+              { V_int (int_of_string (Lexing.lexeme lexbuf)) }
| (['a'-'z']|['A'-'Z']|'_')(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            retrieve_string_tok str }
| ":'"[^''']*'''          { let str = Lexing.lexeme lexbuf in
                            let n = String.length str in
                            V_astring (String.sub str 2 (n-3))}
| '.'                     { T_dot }
| "=="                    { T_eq }
| "!="                    { T_ne }
| ">"                     { T_gt }
| "<"                     { T_lt }
| ">="                    { T_ge }
| "<="                    { T_le }
| '$'['a'-'z']+           { retrieve_setstring_tok (Lexing.lexeme lexbuf) }
| "->"                    { T_arrow }
| ','                     { T_comma }
| '('                     { T_lparen }
| ')'                     { T_rparen } 
| '['                     { T_lbrack }
| ']'                     { T_rbrack }
| '|'                     { T_pipe }
| '='                     { T_equal }
| "*="                    { T_seg }   
