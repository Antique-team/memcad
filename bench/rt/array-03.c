// Ex array-03.c: initialization of an array with unroll
void main() {
  int i;
  int j;
  int t[3];
  i = 0;
  j = 0;
  while(i<3) {
    t[i] = j;
    i = i + 1;
    j = j + 1;
  }
  assert( t[0] == 0 );
  assert( t[1] == 1 );
  assert( t[2] == 2 );
}
