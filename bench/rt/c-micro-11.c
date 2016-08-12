// Ex c-micro-11: malloc, numeric arithmetics
// - malloc
// - simple arithmetic, widening with threshold
// - arithmetic done on a cell referenced to by a pointer
void main( ){
  int * x;
  x = malloc( 4 );
  *x = 0;
  while( *x <= 9 ){
    // passes thanks to the threshold at 10
    *x = *x + 1;
  }
  *x = *x + 1;
  assert( *x == 11 );
}
