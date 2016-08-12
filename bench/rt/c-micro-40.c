// EX c-micro-40: replace_fun_call_by_tmp_var.c
// test function calls inside if's condition
// (transformations MoveFunCall and ReplaceFunCall)
int ret_one() {
  return 1;
}

int ret_one2() {
  return ret_one();
}

int ret_one3() {
  return (ret_one());
}

int set(int* a) {
  *a = 1;
  return 1;
}

int reset(int* a) {
  *a = 0;
  return 1;
}

void some_test(int i, int j) {
  return;
}

void main() {

  int i = 0;
  int x, y;

  if (i = ret_one())
    i = 888;
  assert(i == 888);

  if (ret_one())
    i = 2;
  assert(i == 2);

  if ( ! ret_one())
    i = 3;
  assert(i == 2);

  x = 1;
  y = 2;

  if (ret_one() == x)
    y = 3;
  assert(y == 3);

  if (x == ret_one())
    y = 4;
  assert(y == 4);

  x = -1;
  if ((x = ret_one()) == 1)
    y = 5;
  assert(y == 5);

  x = -1;
  y = -1;
  if (1 == (x = ret_one()))
    y = 5;
  assert(y == 5);

  /* /\* x = y = -1; // FBR: handled by memcad ??? NO !!!!!!! *\/ */
  /* x = -1; */
  /* y = -1; */
  /* if ((x = ret_one()) == (y = ret_one())) */
  /*   y = 6; */
  /* assert(y == 6); */

  i = 2;
  i = ret_one2();
  assert(i == 1);

  i = 2;
  i = ret_one3();
  assert(i == 1);

  i = 3;
  // transform ReplaceFunCall imposes an evaluation order
  // from left to right (and warns about it)
  some_test(set(&i), reset(&i));
  assert(i == 0);
}
