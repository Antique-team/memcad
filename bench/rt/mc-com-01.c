// Ex mc-com-01: MemCAD unroll command
void main( ){
  int x;
  x = 0;
  _memcad( "unroll( 10 )" );
  while( x < 10 ){
    x = x + 1;
  }
  assert( x == 10 );
}
