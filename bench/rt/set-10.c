//lsetin set-10: test inclusion and join! (lsetex)
typedef struct  elist {
  struct elist * next ;
  int data ;
  } elist ;
typedef elist * list ;
void main( ){
  list l ;
  list k ;
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, lsetex, [ | | E ] )" );
  k = null; // nullify, to discard constraint, to remove
  if ( l != 0 ){
    if( l-> next != 0)
      k = l->next->next;
    else
      k = l -> next; }
  else
    k = l;
  _memcad( "check_inductive( l, lsetex, [ | | E] )" );
  // XR: this test is not solved yet!
  //     we need to add a reduction from shapes to set
  // _memcad( "check_inductive( k, lsetex, [ | | F] )" );
}

