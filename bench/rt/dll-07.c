// Ex dll-07: dll reverse, with procedure + globals
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
dll p ;
dll r ;
dll k ;
void reverse( dll l ){
  while( l != 0 ){
    k = l->next;
    l->next = r;
    l->prev = k;
    r = l;
    l = k;
    k = null; // nullify, to discard constraint, to remove
  }
}
void main( ){
  dll m;
  r = null;
  _memcad( "add_inductive( m, dllo, [ r | | ] )" );
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, dllo, [ m | | ] )" );
  reverse( m );
  //_memcad( "unfold( l )" ); // needed to help the next line
  _memcad( "check_inductive( r, dllo, [ m | | ] )" );
}
