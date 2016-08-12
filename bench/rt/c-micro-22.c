// Ex c-micro-20: loop unrolls, and partitioning
void main( ){
  int x;
  int y;
  x = 0;
  y = 10;
  _memcad( "unroll( 5 )" );
  while( x <= 10 ){
    x = x + 1;
    y = y - 1;
  }
  if( x > 2 ){
    assert( y < 8 );
  }
}
