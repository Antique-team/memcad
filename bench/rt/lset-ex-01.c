// Ex lset-ex-01-set: list reversal
typedef struct  elist {
  struct elist * next ;
  int data ;
  } elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  list k ;
  _memcad( "decl_setvars( E, F )" );
  _memcad( "add_inductive( l, lsetex, [ | | E ] )" );
  r = null;
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, lsetex, [ | | F ] )" );
  _memcad( "set_assume (F = $empty )" );
  while( l != 0 ){
    k = l->next;
    l->next = r;
    r = l;
    l = k;
    k = null; // nullify, to discard constraint, to remove
  }
  _memcad( "check_inductive( l, lsetex, [ | | E] )" );
}
