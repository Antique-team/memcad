%{
(** MemCAD analyzer
 **
 ** array_parser.mly
 ** array predicate parser
 ** Jiangchao Liu, 2015/12/21 *)
open Data_structures
open Array_pred_sig
%}
  
%token <int>    V_int
%token <string> V_string

%token T_eof
%token T_semicolon T_comma 
%token T_assign
%token T_and T_or
%token T_equal T_notequal T_lt T_gt T_ge T_le

%token T_lbrace T_rbrace T_lbrack T_rbrack T_lpar T_rpar

%token T_plus T_minus 
%token T_model T_star
%nonassoc Uminus 

%token T_dot 

%token T_forall
%token T_if
%token T_then
%token T_head
%token T_cur
%token T_succ
%token T_compose

%type <Array_pred_sig.numpred>       main_nump
%type <Array_pred_sig.compred>       main_comp
%type <Array_pred_sig.apred>         main_pred
%type <ident>                       identifier
%type <a_arbop>                     arbop
%type <a_combop>                    combop
%type <a_logbop>                    logbop
%type <alval>                       lval
%type <aexpr>                       expr
%type <acond>                       cond

%start main_pred
%%

main_pred:
| main_comp T_eof
    { Comp $1}
| main_nump T_eof
    { Nump $1}

main_nump:
| T_forall identifier T_comma T_if cond T_comma cond
    { { var      = $2;
        assum    = $5;
        solution = $7; } }

main_comp:
| T_compose T_lbrace comps T_rbrace
    { $3 }

comps:
| one_comp 
    { $1::[]}
| T_lpar comps  T_rpar
    { $2}
| comps T_comma comps
    { List.append $1 $3 }

one_comp:
| com_head T_semicolon com_succ T_semicolon cond
    { { head     = $1;
        succ     = $3;
        exitcond = $5; } }

com_head:
| T_head T_assign expr
    { $3 }

com_succ:
| T_succ T_assign expr
    { $3 }

cond:
| expr combop expr 
  { Arith ($2, $1, $3) }
| cond logbop cond
  { Logic ($2, $1, $3) }

expr: 
| V_int
    { Aeconst $1 }
| lval
    { Aelval $1 }
| T_minus expr %prec Uminus
    { Aminus $2 }
| expr arbop expr 
    { Aebin ($2,$1,$3) }
| T_lpar expr T_rpar
    { $2 }

lval:
| V_string
    { Avar (Unrv_var $1) }
| identifier
    { Aident $1 }
| V_string T_lbrack lval T_rbrack T_dot V_string 
    { Aarray_strut (Unrv_var $1, $3, Unrv_off $6) }
| V_string T_lbrack lval T_rbrack 
    { Aarray (Unrv_var $1, $3) }

identifier:
| T_succ
    { Asucc }
| T_cur
    { Acur}

arbop:
| T_plus
    { Abadd }
| T_minus 
    { Absub }
| T_star
    { Abmul }
| T_model
    { Abmod }

combop:
| T_equal
    { Abeq }
| T_notequal
    { Abne }
| T_ge
    { Abge }
| T_le
    { Able }
| T_lt
    { Ablt }
| T_gt
    { Abgt } 

logbop:
| T_and
    { Abland }
| T_or
    { Ablor }
