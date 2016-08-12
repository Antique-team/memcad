// EX c-micro-50: continue.c
// test continue statement's semantic
void main() {

  while (1) {
    assert(1); // reached
    continue;
    assert(0); // never reached
  }
  assert(0); // never reached

}
