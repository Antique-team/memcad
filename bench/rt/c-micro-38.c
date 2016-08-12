// EX c-micro-38: null-stmt.c
// check null statement is handled by a transformation
void main() {
  while (1) // infinitely
    ; // do nothing
}
