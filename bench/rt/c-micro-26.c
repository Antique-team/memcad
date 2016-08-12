// Ex c-micro-26: break (and volatiles)
void main( ){
  int i;
  volatile int c;
  i = 1;
  while( c && i != 0 ){
    if( c ){
      i = 6;
      break;
    }
    i = 0;
  }
  if( i > 4 ){
    _memcad( "check_bottomness( false )" );
  } else {
    _memcad( "check_bottomness( false )" );
  }
}
