// Ex c-micro-31: global variables with initializers
//  test the transformation taking into account var. inits at file scope
int i = 1;
int j = 2;

void main() {
  int k = i + j;
  assert(k == 3);
}
