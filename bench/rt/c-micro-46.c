// EX c-micro-46: rm_comma_binop.c
// test RemoveCommaBinop transformation
int counter = 0;

int fun0() {
  assert(counter == 0);
  ++counter;
  return counter;
}

int fun1() {
  assert(counter == 1);
  ++counter;
  return counter;
}

int fun2() {
  assert(counter == 2);
  return counter;
}

int main() {

  int i = (1, 2);
  assert(i == 2);

  i = (1, 2, 3);
  assert(i == 3);

  i = (1, 2, 3, 4);
  assert(i == 4);

  // check funs are called in the right order
  i = (fun0(), fun1(), fun2(), 3);
  assert(i == 3);
}
