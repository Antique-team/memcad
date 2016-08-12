// TOSORT
// even a simple expression in the return stmt is not handled by memcad
int test() {
  return (1 == 1);
}

void main() {
  assert(test());
}
