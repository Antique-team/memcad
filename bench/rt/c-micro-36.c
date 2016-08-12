// EX c-micro-36: break-multi-assign.c
// test breakMultiAssign

int incr(int* counter) {
  *counter = *counter + 1;
  return *counter;
}

void main() {

  int a, b, c;

  a = b = c = 888; // should just work
  assert(a == 888 && b == 888 && c == 888);

  int counter = 0;
  a = b = c = incr(&counter); // should call incr only once
  assert(a == 1 && b == 1 && c == 1);
}
