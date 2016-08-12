// Ex c-micro-19: variable length malloc
void main( ){
  int * k;
  int i;
  if( i >= 4 ){
    k = malloc( i );
    *k = i;
    assert( *k == i );
  }
}
