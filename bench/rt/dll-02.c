// Ex dll-02: dll extension
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
void main( ){
  dll l ;
  dll p ;
  dll r ;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  if( l != null ){
    r = malloc( 8 );
    r->next = l;
    r->prev = l->prev;
    l->prev = r;
    _memcad( "check_inductive( r, dllo, [ p | | ] )" );
  }
}
