//lsetin set-12, list travel, test inclusion check and join! (lsetin)
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
  k = l; // nullify, to discard constraint, to remove
  while ( k != 0 )
  {
    k = k-> next; 
  }
  _memcad( "check_inductive( l, lsetin, [ | | E] )" );
  _memcad( "check_inductive( k, lsetin, [ | | E] )" );
}
