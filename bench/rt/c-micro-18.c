// Ex c-micro-18: tests that should be performed in the graph

void main( ){
  int x;
  int * p;
  x = 42;
  if( p == &x ){
    assert( *p == 42 );
  }
}
