// Ex c-micro-15: function call
void main( ){
  int * x;
  int y;
  int * z;
  x = & y;
  while( x != null ){
    x = null;
  }
  z = x;
  assert( x == null );
}
