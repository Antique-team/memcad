// Ex c-micro-23: unroll
void main( ){
  volatile int v;
  int x;
  int y;
  int k;
  int delta;
  x = v;
  y = 0;
  k = 0;
  if( x >= 0 ){
    y = 1;
    _memcad( "unroll( 1 )" );
    while( x > 0 ){
      x = x - 1;
      k = 1;
    }
  }
  if( k == 0 ){
    if( y == 0 ){
      _memcad( "check_bottomness( false )" );
    }
  }
  if( k == 0 ){
    if( y == 1 ){
      _memcad( "check_bottomness( false )" );
    }
  }
  if( k == 1 ){
    if( y == 1 ){
      _memcad( "check_bottomness( false )" );
    }
  }
}
