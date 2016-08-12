// Ex array-01.c: static access to an array
void main() {
  int t[2];
  t[1] = 42;
  t[0] = 24;
  assert( t[0] == 24 );
  assert( t[1] == 42 );
}
