// Ex dll-19: dll traversal
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
void main( ){
  dll l ;
  dll p ;
  dll c ;
  dll p0;
  dll l0;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  _memcad( "add_inductive( l0, dllo, [ p0 | | ] )" );
  //if( l0 == l ){
  //  _memcad( "check_inductive( l0, dllo, [ p0 | | ] )" );
  //}
  if( l0 != null ){
    if( l != null ){
      if( l0 == l ){
        _memcad( "check_bottomness( true )" );
      }
    }
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
