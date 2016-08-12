// Ex array-00.c: static access to an array
void main() {
  int t[2];
  t[0] = 24;
  t[1] = 42;
  assert( t[0] == 24 );
  assert( t[1] == 42 );
}
