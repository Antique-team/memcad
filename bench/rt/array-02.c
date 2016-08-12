// Ex array-02.c: initialization of an array with unroll
void main() {
  int i;
  int t[3];
  i = 0;
  while(i<3) {
    t[i] = i;
    i = i + 1;
  }
  assert( t[0] == 0 );
  assert( t[1] == 1 );
  assert( t[2] == 2 );
}
