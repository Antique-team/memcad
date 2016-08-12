// Ex c-micro-07: basic use of break
void main( ){
  int x = 0;
  while( x <= 10 ){
    x = 1;
    break;
  }
  assert( x <= 1 );
}
