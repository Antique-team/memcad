// EX c-micro-41: unary_not.c
// test unary logical not operator
void main() {
  int i = 1;
  if ( ! 0 ) {
    i = 5;
  }
  assert(i == 5);
}
