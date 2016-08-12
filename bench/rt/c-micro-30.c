// Ex: c-micro-30.c, modulo test
int clamp( int i, int min, int max ){
  int r;
  if( i <= min ){
    r = min;
  } else if( max <= i ){
    r = max;
  } else {
    r = i;
  }
  return r;
}
void main( ){
  int x;
  int y;
  int xc;
  int yc;
  int r;
  xc = clamp( x, 0, 12 );
  r = xc % 15;
  assert( 0 <= r );
  assert( r <= 12 );
  yc = clamp( y, 3, 4 );
  r = xc % yc;
  assert( 0 <= r );
  assert( r <= 3 );
}
