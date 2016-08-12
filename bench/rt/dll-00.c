// Ex dll-00: dll ptr copy
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
  r = l;
  _memcad( "check_inductive( r, dllo, [ p | | ] )" );
}
