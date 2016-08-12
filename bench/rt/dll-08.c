// Ex dll-08: dll traversal
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
  c = l;
  while( c != 0 ){
    c = c->next;
  }
  assert( p == p ); // temporary, to force keeping p live!
  _memcad( "check_inductive( l, dllo, [ p | | ] )" ); // should it keep p live ?
}
