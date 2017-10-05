// Ex c-micro-61: exit statement

void main( ){
  int x = 0;
  int y;
  if( y < 0 ){
    exit( 0 );
    x = 1;
  }
  assert( x == 0 );
}
