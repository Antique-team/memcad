// Ex c-micro-07: break and variables creation
void main( ){
  int z;
  int x = 0;
  if( z > 0 ){
    while( x <= 10 ){
      int y = 1;
      x = y + x;
      if( x > 5 ){
        int h = 0;
        break;
      }
    }
  }
  assert( x <= 11 );
  x = 4;
}
