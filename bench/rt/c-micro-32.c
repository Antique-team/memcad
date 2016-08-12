// EX c-micro-32: --i.c
/* test --i transformation works */
void main() {
  int i = 5;
  --i;
  assert(i == 4);
}
