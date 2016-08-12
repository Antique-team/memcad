// Ex c-micro-16: check_bottomness regression test command
void main( ){
  int x;
  x = 24;
  if( x < 42 ){
    _memcad( "check_bottomness( false )" );
  } else {
    _memcad( "check_bottomness( true )" );
  }
}
