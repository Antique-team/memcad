// Ex dll-15: dll traversal + backward traversal
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
    dll d;
    dll e;
    d = c;
    _memcad( "unroll( 1 )" );
    while( d != l && cond ){
      // the localization of d is lost on that edge
      // so, d appears on no segment at all
      d = d->prev;
    }
    e = d->prev;
    _memcad( "check_inductive( d, dllo, [ e | | ] )" );
    //_memcad( "force_live( c )" );
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
