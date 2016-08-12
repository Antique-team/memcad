// EX c-micro-44: for_to_while.c
// test the ForToWhile transformation
void main() {

  int i;
  int j;
  int count;

  for (i = 0 ; i < 2 ; ++i) {
    for (j = 0 ; j < 2 ; ++j) { // imbricated
      count = 1;
    }
    assert(j >= 2);
  }
  assert(i >= 2);

  for (i = 0 ; i < 2 ; ++i) // empty body
    {}
  assert(i >= 2);

  i = -1;
  for (i = 0 ; i < 2 ; ) { // no increment
    ++i;
  }
  assert(i >= 2);

  i = 0;
  for ( ; i < 2 ; ++i) { // no init
  }
  assert(i >= 2);

  for ( ; ; ) { // infinite loop
    i = 888;
  }
  assert(0); // never reached
}
