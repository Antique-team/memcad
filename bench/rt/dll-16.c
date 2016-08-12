// Ex dll-16: dll traversal + backward traversal, if hack
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
    //dll e;
    d = c;
   // _memcad( "unroll( 1 )" );
    while( d != l ){
      d = d->prev;
      if( d != l){
        dll foo;
	foo = d->next;
      }
    }
    //e = d->prev;
    //_memcad( "check_inductive( d, dllo, [ e | | ] )" );
    _memcad( "force_live( l, c, d )" );
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
