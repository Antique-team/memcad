// Ex mc-com-00: basic arithmetics
void main( ){
  int x ;
  if( x ){
    x = 0;
  } else {
    x = 4;
    _memcad( "kill_flow" );
  }
  assert( x == 0 );
}
