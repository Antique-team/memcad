
int f(int i, int j) {
  return (i && j);
}

int g(int i, int j) {
  return (i == j);
}

// test the assignCond transform
void main() {

  char* ptr = 0;
  int i;
  int j = 2;
  int k = 3;

  i = 0;
  i = ptr == 0; // 1)
  assert(i == 1);
  i = 0;
  i = (ptr == 0); // same as 1) but between parentheses
  assert(i == 1);
  i = 0;
  i = (j < k); // 2)
  assert(i);

  int l = 1 == 2;
  assert(l == 0);
  int m = !(1 == 2);
  assert(m);

  int n = 1 && 0;
  assert(!n);
  n = 0 || 1;
  assert(n);

  assert(f(1, 1));

  assert(g(3, 3));
}
