// Ex: c-micro-29.c, modulo test
void main( ){
  int x;
  int xc;
  int r;
  if( x <= 0 ){
    xc = 0;
  } else if( 12 <= x ){
    xc = 12;
  } else {
    xc = x;
  }
  r = xc % 15;
  assert( 0 <= r );
  assert( r <= 12 );
}
