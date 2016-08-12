//lsetex set-11, list travel, test inclusion check and join! (lsetex)
typedef struct  elist {
  struct elist * next ;
  int data ;
  } elist ;
typedef elist * list ;
void main( ){
  list l ;
  list k ;
  _memcad( "decl_setvars( E, F )" );
  _memcad( "add_inductive( l, lsetex, [ | | E ] )" );
  _memcad( "set_assume( F = $empty )" );
  k = l; // nullify, to discard constraint, to remove
  while ( k != 0 )
  {
    k = k-> next; 
  }
  _memcad( "check_inductive( l, lsetex, [ | | E] )" );
  // XR: this test is not solved yet!
  //     we need to add a reduction from shapes to set!
  // _memcad( "check_inductive( k, lsetex, [ | | F] )" );
}
