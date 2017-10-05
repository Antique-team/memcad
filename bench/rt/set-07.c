// Ex set-07: test inclusion check! (lsetex)
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
  _memcad( "set_assume( F $sub E )" );
  k = null; // nullify, to discard constraint, to remove
  if ( l != 0 ){
    k = l->next; }
  else
    k = l;
  _memcad( "check_inductive( l, lsetex, [ | | E] )" );
  // XR: this test seems unsound to me
  //     (it now fails ---seems rightfully so to me--- and it used not to...)
  // _memcad( "check_inductive( k, lsetex, [ | | F] )" );
  _memcad("output_dot(l, k | SUCC)");
}
