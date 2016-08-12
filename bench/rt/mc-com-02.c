// Ex mc-com-02: partitioning tokens
void main( ){
  int i;
  int j;
  i = 0;
  if( i < 4 ){
    i = 5;
  }
  if( j > 2 ){
    j = 2;
  }
  assert( i - j > 0 );
  _memcad( "merge()" );
  i = j;
}
