// EX c-micro-35: break.c
// test break statement's semantic
void main() {

  while (1) {
    assert(1); // reached
    break;
    assert(0); // never reached
  }
  assert(1); // reached

}
