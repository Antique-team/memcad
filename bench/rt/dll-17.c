// Ex dll-17: dll traversal + backward traversal, unfold_bseg
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
void main( ){
  dll l;
  dll p;
  dll c;
  p = null;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  c = l;
  {
    volatile int cond;
    while( c != null && cond ){
      c = c->next;
    }
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
  if( c != null ){
    dll d;
    d = c;
    while( d != l ){
      dll e;
      e = d->prev;
      _memcad( "unfold_bseg( d )" );
      d = e;
    }
    _memcad( "force_live( l, c, d )" );
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
