// EX c-micro-50: enums.c
// test partial handling for enum types
enum toto { ONE, TWO, THREE = 3, FOUR } ;

void main() {

  int i = ONE;
  assert(i == 0);
  i = TWO;
  assert(i == 1);
  i = THREE;
  assert(i == 3);
  i = FOUR;
  assert(i == 4);
}
