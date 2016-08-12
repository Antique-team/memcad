// EX c-micro-43: do_while_to_while.c
// test the DoWhileToWhile transformation
void main() {

  int i = 0;
  int j = 0;

  do {
    j = 1;
  } while (0); // never loop; just do once
  assert(j == 1); // do's body was executed

  do {
    ++i;
  } while (i < 3);
  assert(i >= 3); // loop was executed
}
