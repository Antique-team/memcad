// TOSORT
// Ex XXX: test the result of a function can be ignored when necessary

int ret_one() {
  return 1;
}

int i;

int function_f() {
  return i++;
}

#define TRUE 1
#define FALSE 0

void main() {

  ret_one();

  if (ret_one() == 1) assert(TRUE);
  else assert(FALSE);

  i = 0;

  function_f();

  assert(i == 1);

  int res = function_f();

  assert(res == 1);
  assert(i == 2);
}
