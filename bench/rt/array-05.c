// Ex array-05.c: initialization of an array, last elt test
void main() {
  int i;
  int t[10];

  i = 0;
  while(i<10) {
    t[i] = 99;
    i = i + 1;
  }
  i = i - 1;
  assert( t[i] == 99 );
}
