// Ex c-micro-13: function call
int abs( int y ){
  int r;
  if( y >= 0 ){
    r = y;
  } else {
    r = -y;
  }
  return r;
}
void main( ){
  int x ;
  int res ;
  res = abs( x );
  assert( res >= 0 );
}
