// Ex dll-09: dll free
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
void main( ){
  dll l ;
  dll p ;
  dll c ;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  while( l != 0 ){
    c = l->next;
    if( c != null ){
      c->prev = l->prev;
    }
    free( l );
    l = c;
  }
  assert( p == p ); // temporary, to force keeping p live!
  _memcad( "check_inductive( l, dllo, [ p | | ] )" ); // should it keep p live ?
}
