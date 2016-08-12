// Ex dll-12: dll traversal + 1 step back
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
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  c = l;
  while( c != null && cond ){
    c = c->next;
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
  if( c != null ){
    dll d;
    d = c->prev;
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
