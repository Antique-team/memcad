// Ex: c-micro-28.c, modulo test
void main( ){
  int x;
  int r;
  if( 0 <= x ){
    if( x <= 12 ){
      r = x % 15;
      assert( 0 <= r );
      assert( r <= 12 );
    }
  }
}
