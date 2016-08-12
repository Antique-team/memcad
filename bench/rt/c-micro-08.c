// Ex c-micro-08: loop counter, through fields
// straightforward iteration based on a counter
// yet, the variable being incremented is in a structure
typedef struct t {
  int useless ;
  int n ;
} t;

void main( ){
  t x;
  int k;
  x.n = 0;
  while( x.n < 10 ){
    x.n = x.n + 1;
  }
  assert( x.n <= 10 );
  k = 0;
}
