// EX c-micro-37: break-op-assign.c
// test breakOpAssign transformation
void main() {

  int a = 0;

  a += 1;
  assert(a == 1);
  a *= 2;
  assert(a == 2);
  a /= 2;
  assert(a == 1);
  a += 2;
  a %= 3;
  assert(a == 0);
}
