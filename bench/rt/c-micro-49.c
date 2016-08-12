// EX c-micro-49: local_fun_fwd_decl.c

void main() {
  int ret_one(); // local forward decl.
  int i = ret_one();
  assert(i == 1);
}

int ret_one() {
  return 1;
}
