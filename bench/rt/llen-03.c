// Ex llen-03: llen reversal
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  list k ;
  _memcad( "add_inductive( l, slllo, [ |100| ] )" );
  r = null;
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, slllo, [ |0| ] )" );
  while( l != 0 ){
    k = l->next;
    l->next = r;
    r = l;
    l = k;
    k = null; // nullify, to discard constraint, to remove
  }
  _memcad( "unfold( l )" ); // needed to help the next line
  // _memcad( "check_inductive( l, slllo, [ |0| ] )" );
  _memcad( "check_inductive( r, slllo, [ |100| ] )" );
}
