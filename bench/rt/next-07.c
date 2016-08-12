// a series of simple arithmetic tests
void main( ){
  int x;
  int y;
  int z;
  if( 0 <= x ){
    if( 5 <= y ){
      z = x + y;
      assert( 5 <= z );
    }
  }
  if( 8 <= x ){
    if( y <= 5 ){
      z = x - y;
      assert( 3 <= z );
    }
  }
}
