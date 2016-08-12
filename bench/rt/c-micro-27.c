// Ex c-micro-27: break (and volatiles)
void main( ){
  int i;
  i = 0;
  while( 1 ){
    i = i + 1;
    if( i >= 10 ){
      break;
    }
    assert( i < 10 );
  }
  i = i + 1;
  _memcad( "check_bottomness( false )" );
}
