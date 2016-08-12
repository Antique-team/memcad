// EX c-micro-42: move_assign_before_test.c
// test the MoveAssignBeforeTest AST transformation
void main() {

  int i = 0;
  int j = 1;

  if ((i = j) == 1) {
    assert(i == 1);
  }

  if (2 == (i = 2)) {
    assert(i == 2);
  }

}
