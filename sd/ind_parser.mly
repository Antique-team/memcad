%{
(** MemCAD analyzer
 **
 ** ind_parser.mly
 ** inductive definitions parser
 ** Xavier Rival, 2011/05/22 *)
open Data_structures
open Graph_sig
open Ind_sig
open Sv_sig
let make_map: 'a list -> 'a IntMap.t =
  let rec aux i acc l =
    match l with
    | [ ] -> acc
    | x :: y -> aux (i+1) (IntMap.add i x acc) y in
  aux 0 IntMap.empty
%}
  
%token <int>    V_int
%token <int>    V_size_contains
%token <string> V_string

%token <int>    V_par_int
%token <int>    V_par_ptr
%token <int>    V_par_set

%token <int>    V_new_var

%token T_at T_arrow T_contains T_defeq T_notequal
%token T_setmem T_setequal

%token T_lt T_gt T_colon T_comma T_dot T_pipe
%token T_lbrace T_rbrace T_lbrack T_rbrack T_lpar T_rpar
%token T_equal
%token T_and T_plus T_minus T_star

%token T_eof

%token T_alloc
%token T_addr
%token T_emp
%token T_int
%token T_prec
%token T_raw
%token T_set
%token T_this

%type <Ind_sig.p_iline list>        main_ilines
%type <Ind_sig.ind list>            main_indlist
%type <Ind_sig.ind>                 main_ind
%type <ind>                         inductive
%type <irule list>                  irules
%type <irule>                       irule
%type <int * ntyp list>             nvars
%type <ntyp list>                   opt_ntypes
%type <ntyp>                        ntype
%type <hform>                       fheap
%type <hform>                       theap
%type <cell>                        cell
%type <indcall>                     indcall
%type <formal_main_arg>             indpoint
%type <formal_int_args>             intargs
%type <pform>                       fpure
%type <pformatom>                   tpure
%type <Ind_sig.pformatom>           tpurealloc
%type <sform>                       tpureset
%type <aform>                       tpurearith
%type <aexpr>                       tarith
%type <aexpr>                       tarith0
%type <aexpr>                       tarith1
%type <sexpr>                       sterm
%type <formal_int_arg>              iatom
%type <Offs.t>                      field
%type <string list>                 string_list

%start main_ilines main_indlist main_ind
%%

main_ilines:
| T_eof
    { [ ] }
| inductive main_ilines
    { Piind $1 :: $2 }
| T_prec T_colon string_list T_dot main_ilines
    { Piprec $3 :: $5 }
| V_string T_colon V_string T_dot main_ilines
    { Pibind ($1, $3) :: $5 }

main_indlist:
| T_eof
    { [ ] }
| inductive main_indlist
    { $1 :: $2 }

main_ind:
| inductive T_eof
    { $1 }

inductive:
| V_string T_lt V_int T_comma V_int T_gt T_defeq irules T_dot
    { { i_name    = $1 ;
        i_ppars   = $3 ;
        i_ipars   = $5 ;
        i_spars   = 0 ;
        i_rules   = $8;
        i_srules  = $8;
        i_mt_rule = false;
        i_emp_ipar = -1;
        i_reds0   = false;
        i_dirs    = Offs.OffSet.empty;
        i_may_self_dirs = Offs.OffSet.empty;
        i_pr_pars = IntSet.empty;
        i_fl_pars = IntMap.empty;
        i_pr_offs = Offs.OffSet.empty;
        i_list    = None;
        i_pkind   = Ind_utils.pars_rec_top; } }
| V_string T_lt V_int T_comma V_int T_comma V_int T_gt T_defeq irules T_dot
    { { i_name    = $1 ;
        i_ppars   = $3 ;
        i_ipars   = $5 ;
        i_spars   = $7 ;
        i_rules   = $10;
        i_srules  = $10;
        i_mt_rule = false;
        i_emp_ipar = -1;
        i_reds0   = false;
        i_dirs    = Offs.OffSet.empty;
        i_may_self_dirs = Offs.OffSet.empty;
        i_pr_pars = IntSet.empty;
        i_fl_pars = IntMap.empty;
        i_pr_offs = Offs.OffSet.empty;
        i_list    = None;
        i_pkind   = Ind_utils.pars_rec_top; } }

irules:
|
    { [ ] }
| irule irules
    { $1 :: $2 }

irule:
| T_pipe nvars T_minus fheap T_minus fpure
    { let n, t = $2 in { ir_num   = n;
                         ir_typ   = make_map t;
                         ir_heap  = $4;
                         ir_pure  = $6;
                         ir_kind  = Ik_unk;
                         ir_uptr  = IntSet.empty;
                         ir_uint  = IntSet.empty;
                         ir_uset  = IntSet.empty;
                         ir_unone = false; } }

nvars:
| T_lbrack V_int opt_ntypes T_rbrack
    { $2, $3 }

opt_ntypes:
|   { [ ] }
| ntype opt_ntypes
    { $1 :: $2 }

ntype:
| T_addr   { Ntaddr }
| T_int    { Ntint }
| T_raw    { Ntraw }
| T_set    { Ntset }

fheap:
| theap
    { $1 }
| theap T_star fheap
    { $1 @ $3 }

theap:
| T_emp
    { [ ] }
| cell
    { [ Hacell $1 ] }
| indcall
    { [ Haind $1 ] }

cell:
| T_this T_arrow field T_contains aatom
    { { ic_off  = $3;
        ic_size =  4;
        ic_dest = $5 } }
| T_this T_arrow field V_size_contains aatom
    { { ic_off  = $3;
        ic_size = $4;
        ic_dest = $5 } }

indcall:
| indpoint T_dot V_string T_lpar indargs T_rpar
    { let p, i, s = $5 in { ii_maina = $1;
                            ii_ind   = $3;
                            ii_argp  = p ;
                            ii_argi  = i ;
                            ii_args  = s } }

indpoint:
| T_this
    { `Fa_this }
| V_new_var
    { `Fa_var_new $1 }

indargs:
|
    { [ ], [ ], [ ] }
| ptrargs T_pipe intargs T_pipe setargs
    { $1, $3, $5 }

ptrargs:
|
    { [ ] }
| patom
    { [ $1 ] }
| patom T_comma ptrargs
    { $1 :: $3 }

intargs:
|
    { [ ] }
| iatom
    { [ $1 ] }
| iatom T_comma intargs
    { $1 :: $3 }

setargs:
|
    { [ ] }
| satom
    { [ $1 ] }
| satom T_comma setargs
    { $1 :: $3 }

fpure:
|
    { [ ] }
| tpure
    { [ $1 ] }
| tpure T_and fpure
    { $1 :: $3 }

tpure:
| tpurealloc
    { $1 }
| tpurearith
    { Pf_arith $1 }
| tpureset
    { Pf_set $1 }

tpurealloc:
| T_alloc T_lpar T_this T_comma V_int T_rpar
    { Pf_alloc $5 }

tpureset:
| aatom T_setmem satom
    { Sf_mem ($1, $3) }
| satom T_setequal sterm
    { Sf_equal ($1, $3) }
| satom T_setequal T_lbrace T_rbrace
    { Sf_empty $1 }

tpurearith:
| tarith T_equal tarith
    { Af_equal ($1, $3) }
| tarith T_notequal tarith
    { Af_noteq ($1, $3) }

tarith:
| tarith0
    { $1 }

tarith0:
| tarith1
    { $1 }
| tarith0 T_plus tarith1
    { Ae_plus ($1, $3) }

tarith1:
| V_int
    { Ae_cst $1 }
| aatom
    { Ae_var $1 }

sterm:
| satom
    { Se_var $1 }
| satom T_plus T_lbrace aatom T_rbrace
    { Se_uplus ($1, $4) }

patom:
| T_this
    { `Fa_this }
| V_new_var
    { `Fa_var_new $1 }
| V_par_ptr
    { `Fa_par_ptr $1 }

iatom:
| V_new_var
    { `Fa_var_new $1 }
| V_par_int
    { `Fa_par_int $1 }

satom:
| V_new_var
    { `Fa_var_new $1 }
| V_par_set
    { `Fa_par_set $1 }

aatom:
| T_this
    { `Fa_this }
| V_new_var
    { `Fa_var_new $1 }
| V_par_ptr
    { `Fa_par_ptr $1 }
| V_par_int
    { `Fa_par_int $1 }

field:
| V_string
    { Offs.of_string $1 }
| V_int
    { Offs.of_int $1 }

string_list:
| { [ ] }
| V_string string_list { $1 :: $2 }
