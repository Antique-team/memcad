// Ex c-micro-14: procedure call, return with no expression
int r;
void abs( int y ){
  if( y >= 0 ){
    r = y;
    return;
  }
  r = -y;
}
void main( ){
  int x ;
  int res ;
  abs( x );
  res = r;
  assert( res >= 0 );
}
