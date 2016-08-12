// Ex c-micro-56: basic use of continue
void main( ){
  int x = 0;
  int y = 0;
  while( x <= 10 ){
    x = x + 1;
    int z = 1;
    y = z;
    continue;
    y = 2;
  }
  assert( y <= 1 );
}
