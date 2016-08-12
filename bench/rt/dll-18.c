// Ex dll-18: dll traversal + backward traversal, unfold_bseg
//  removing the force_live command
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
    // TODO: remove this force_live command
    //       it is due to the fact c is not live, so the point
    //       until which segment from d is to be unfolded is not
    //       clear
    _memcad( "force_live( c )" );
  }
  // _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
