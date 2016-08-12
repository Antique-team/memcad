// EX c-micro-48: fun_ret_types.c

int ret_one() {
  return 1;
}

char ret_a() {
  return 'a';
}

void main() {
  char a = ret_a();
  int one = ret_one();
  assert(a == 'a');
  assert(one == 1);
}
