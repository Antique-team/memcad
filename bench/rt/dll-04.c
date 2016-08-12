// Ex dll-04: dll reverse, with global variables
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
dll l ;
dll p ;
dll r ;
dll k ;
void main( ){
  r = null;
  _memcad( "add_inductive( l, dllo, [ r | | ] )" );
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, dllo, [ l | | ] )" );
  while( l != 0 ){
    k = l->next;
    l->next = r;
    l->prev = k;
    r = l;
    l = k;
    k = null; // nullify, to discard constraint, to remove
  }
  _memcad( "unfold( l )" ); // needed to help the next line
  _memcad( "check_inductive( r, dllo, [ l | | ] )" );
}
