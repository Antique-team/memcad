// Ex c-micro-12: procedure call
int r;
void abs( int y ){
  if( y >= 0 ){
    r = y;
  } else {
    r = -y;
  }
}
void main( ){
  int x ;
  abs( x );
  assert( r >= 0 );
}
