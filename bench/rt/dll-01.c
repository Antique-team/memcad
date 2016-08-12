// Ex dll-01: dll step
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
void main( ){
  dll l ;
  dll p ;
  dll r ;
  dll m ;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  if( l != null ){
    r = l;
    m = r->next;
    _memcad( "check_inductive( m, dllo, [ l | | ] )" );
  }
}
