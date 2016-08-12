// Ex array-07.c: initialization of an array (2 steps, no unroll)
typedef struct foo {
  int * p;
  int   i;
} foo;

void main() {
  int i;
  foo t[10];

  i = 0;
  while(i<10) {
    t[i].p = null;
    t[i].i = 24;
    i = i + 1;
  }
  i = i - 1;
  //assert( t[i].p == null );
  // => this assetion could not be proved (all cells abstract)
  //assert( t[i].i == 24 );
  // => this assertion could not be analyzed with no crash
  //    unless we add a congruence abstraction
}
