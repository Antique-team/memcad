// EX c-micro-47: file_scope_inits.c
/* test the transformation taking into account var. inits at file scope */
int i = 1;
int j = 2;

void main() {
  int k = i + j;
  assert(k == 3);
}
