// Ex shape-less-00:
//  code manipulating shape-less memory, i.e., no inductive structure

void main( ){
  int a;
  int b;
  int c;
  int d;
  int res;
  int u;
  int v;
  res = 0;
  a = 4;
  b = a + res;
  assert( b < 10 );
}
