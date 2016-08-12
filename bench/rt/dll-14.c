// Ex dll-14: dll traversal + 2 steps back + check 1
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
volatile int cond;
void main( ){
  dll l;
  dll p;
  dll c;
  p = null;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  c = l;
  while( c != null && cond ){
    c = c->next;
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
  if( c != null ){
    dll d0;
    d0 = c->prev;
    if( d0 != null ){
      dll d1;
      d1 = d0->prev;
      _memcad( "check_inductive( d0, dllo, [ d1 | | ] )" );
      if( d1 != null ){
        dll d2;
        d2 = d1->prev;
        _memcad( "check_inductive( d1, dllo, [ d2 | | ] )" );
      }
    }
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
