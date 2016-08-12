// Ex c-micro-24: degenerated loops (1)
void main( ){
  int i;
  i = 0;
  while( 0 ){
    _memcad( "check_bottomness( true )" );
    i = 1;
  }
  assert( i == 0 );
  _memcad( "check_bottomness( false )" );
}
