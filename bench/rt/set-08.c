// Ex set-08: test inclusion check (lsetin)
typedef struct  elist {
  struct elist * next ;
  int data ;
  } elist ;
typedef elist * list ;
void main( ){
  list l ;
  list k ;
  _memcad( "decl_setvars( E )" );
  _memcad( "add_inductive( l, lsetin, [ | | E ] )" );
  k = null; // nullify, to discard constraint, to remove
  if ( l != 0 )
    k = l->next;
  else
    k = l;
  _memcad( "check_inductive( l, lsetin, [ | | E] )" );
  _memcad( "check_inductive( k, lsetin, [ | | E] )" );
  _memcad("output_dot(l, k | SUCC)");
}
