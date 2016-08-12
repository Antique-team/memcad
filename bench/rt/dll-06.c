// Ex dll-06: dll traversal
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
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
