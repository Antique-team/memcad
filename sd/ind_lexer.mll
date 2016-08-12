(** MemCAD analyzer
 **
 ** ind_lexer.mll
 ** inductive definitions lexer
 ** Xavier Rival, 2011/05/22 *)
{
open Ind_parser
open Graph_sig
open Graph_utils
(* Integer tokens extraction *)
let extract_p i s =
  let n = String.length s in
  assert (n > i);
  int_of_string (String.sub s i (n-i))
(* Extraction of the size out of an arrow *)
let extract_size_arrow (s: string): int =
  let n = String.length s in
  assert (n > 3);
  int_of_string (String.sub s 1 (n-3))
(* String token hashes *)
let hash_string_tokens = Hashtbl.create 10
let _ =
  let lst_string_tokens =
    [ "alloc",    T_alloc ;
      "addr",     T_addr ;
      "emp",      T_emp ;
      "int",      T_int ;
      "prec",     T_prec ;
      "raw",      T_raw ;
      "set",      T_set ;
      "this",     T_this ] in
  List.iter (fun (str, tok) -> Hashtbl.add hash_string_tokens str tok)
    lst_string_tokens
let retrieve_string_tok (s: string) =
  try Hashtbl.find hash_string_tokens s
  with Not_found -> V_string s
}

rule token = parse
| ' ' | '\t'              { token lexbuf }
| '\n'                    { incr Lex_lib.num_line; token lexbuf }
| '%'[^'\n']*'\n'   (* line of comments *)
                          { incr Lex_lib.num_line; token lexbuf }
| '@''i'(['0'-'9'])+      { V_par_int (extract_p 2 (Lexing.lexeme lexbuf)) }
| '@''p'(['0'-'9'])+      { V_par_ptr (extract_p 2 (Lexing.lexeme lexbuf)) }
| '@''s'(['0'-'9'])+      { V_par_set (extract_p 2 (Lexing.lexeme lexbuf)) }
| '$'(['0'-'9'])+         { let n = extract_p 1 (Lexing.lexeme lexbuf) in
                            V_new_var n }
| "|-"['0'-'9']+'-''>'    { let str = Lexing.lexeme lexbuf in
                            V_size_contains (extract_size_arrow str) }
| ['0'-'9']+              { V_int (int_of_string (Lexing.lexeme lexbuf)) }
| (['a'-'z']|['A'-'Z']|'_')(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            retrieve_string_tok str }
| "->"                    { T_arrow }
| ':'                     { T_colon }
| "|->"                   { T_contains }
| ":="                    { T_defeq }
| "!="                    { T_notequal }
| "=="                    { T_setequal }
| '#'                     { T_setmem }
| '<'                     { T_lt }
| '>'                     { T_gt }
| ','                     { T_comma }
| '.'                     { T_dot }
| '|'                     { T_pipe }
| '{'                     { T_lbrace }
| '}'                     { T_rbrace }
| '['                     { T_lbrack }
| ']'                     { T_rbrack }
| '('                     { T_lpar }
| ')'                     { T_rpar }
| '='                     { T_equal }
| '&'                     { T_and }
| '+'                     { T_plus }
| '-'                     { T_minus }
| '*'                     { T_star }
| eof                     { T_eof }
