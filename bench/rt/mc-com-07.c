// test memcad assume command
void main() {
  int i, j;
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
}
