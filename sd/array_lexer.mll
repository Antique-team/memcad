(** MemCAD analyzer
 **
 ** array_lexer.mll
 ** array predicates lexer
 ** Jiangchao Liu, 2015/12/21 *)
{
open Array_parser
open Graph_sig
open Graph_utils
(* String token hashes *)
let hash_keyword_tokens = Hashtbl.create 10
let _ =
  let lst_keyword_tokens =
    [ "Forall",    T_forall ;
      "If",        T_if ;
      "Then",      T_then ;
      "Compose",   T_compose ] in
  List.iter (fun (str, tok) -> Hashtbl.add hash_keyword_tokens str tok)
    lst_keyword_tokens
let retrieve_keyword_tok (s: string) =
  try Hashtbl.find hash_keyword_tokens s
  with Not_found -> V_string s
let hash_identifier_tokens = Hashtbl.create 10
let _ =
  let lst_identifier_tokens =
    [ "Head",     T_head ;
      "Cur",      T_cur ;
      "Succ",     T_succ ] in
  List.iter (fun (str, tok) -> Hashtbl.add hash_identifier_tokens str tok)
    lst_identifier_tokens
let retrieve_identifier_tok (s: string) =
  try Hashtbl.find hash_identifier_tokens s
  with Not_found -> V_string s
}

rule token = parse
| ' ' | '\t'              { token lexbuf }
| '\n'                    { incr Lex_lib.num_line; token lexbuf }
| '#'[^'\n']*'\n'   (* line of comments *)
                          { incr Lex_lib.num_line; token lexbuf }
| '$'(['A'-'Z'])(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            let len = String.length str in
                            retrieve_identifier_tok
                              (String.sub str 1 (len - 1)) }
| ['0'-'9']+              { V_int (int_of_string (Lexing.lexeme lexbuf)) }
| (['a'-'z']|['A'-'Z']|'_')(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            retrieve_keyword_tok str }
| "!="                    { T_notequal }
| "=="                    { T_equal }
| '<'                     { T_lt }
| '>'                     { T_gt }
| "<="                    { T_le }
| ">="                    { T_ge }
| ','                     { T_comma }
| ';'                     { T_semicolon }
| '.'                     { T_dot }
| '{'                     { T_lbrace }
| '}'                     { T_rbrace }
| '['                     { T_lbrack }
| ']'                     { T_rbrack }
| '('                     { T_lpar }
| ')'                     { T_rpar }
| '='                     { T_assign }
| "&&"                    { T_and }
| "||"                    { T_or }
| '+'                     { T_plus }
| '-'                     { T_minus }
| '*'                     { T_star }
| '%'                     { T_model }
| eof                     { T_eof }
