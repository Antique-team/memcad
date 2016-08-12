%{
(** MemCAD analyzer
 **
 ** domsel_parser.mly
 ** domain structure parser
 ** Xavier Rival, 2012/04/05 *)
open Flags
%}

%token <string>   V_string

%token T_lpar T_rpar T_lbrack T_rbrack T_and T_star T_comma T_underscore
%token T_all T_list
%token T_eof

%type <Flags.shape_dom>  edomshape
%type <Flags.shape_dom>  domshape0
%type <Flags.shape_dom>  domshape1
%type <string list>      indlist

%start edomshape
%%

edomshape:
| domshape0 T_eof                { $1 }

domshape0:
| domshape0 T_star domshape1     { Shd_sep ($1, $3) }
| domshape1                      { $1 }

domshape1:
| domshape1 T_and domshape2      { Shd_prod ($1, $3) }
| domshape2                      { $1 }

domshape2:
| T_lbrack T_underscore T_rbrack { Shd_flat    }
| T_lbrack T_all T_rbrack        { Shd_all     }
| T_lbrack T_list T_rbrack       { Shd_list    }
| T_lbrack indlist T_rbrack      { Shd_inds $2 }
| T_lpar domshape0 T_rpar        { $2          }

indlist:
| { [ ] }
| V_string { [ $1 ] }
| indlist T_comma V_string       { $3 :: $1 }
