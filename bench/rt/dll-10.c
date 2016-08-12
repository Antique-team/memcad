// Ex dll-10: dll complete free
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
volatile int cond;
void main( ){
  dll l ;
  dll p ;
  dll c ;
  p = null;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  if( l != null ){
    while( l->next != null ){
      dll c;
      c = l->next;
      c->prev = l->prev;
      free( l );
      l = c;
      _memcad( "check_inductive( l, dllo, [ p | | ] )" );
    }
    free( l );
    l = null;
  }
  assert( l == null );
}
