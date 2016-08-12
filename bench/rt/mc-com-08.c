// mc-com-08: test memcad assume command
void main() {
  int i, j, k;
  _memcad( "assume(i != 0)"); // add numerical precondition
  assert(i != 0);             // check it
  _memcad( "assume(j != 77)");
  assert(j != 77);
  _memcad( "assume(i != j)");
  assert(i != j);
  _memcad( "assume(i == j)");
  assert(i == j);
  _memcad( "assume(i <= j)");
  assert(i <= j);
  _memcad( "assume(i < j)");
  assert(i < j);
  _memcad( "assume(i >= j)");
  assert(i >= j);
  _memcad( "assume(i > j)");
  assert(i > j);
  _memcad( "assume(i == 1, j == 2, k == 3)");
  assert(i + j + k == 6);
}
