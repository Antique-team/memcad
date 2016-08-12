// Ex c-micro-25: degenerated loops (2)
void main( ){
  int i;
  i = 0;
  while( 1 ){
    _memcad( "check_bottomness( false )" );
    i = 1;
  }
  _memcad( "check_bottomness( true )" );
}
