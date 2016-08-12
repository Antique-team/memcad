// Ex shape-less-01:
//  code manipulating shape-less memory, i.e., no inductive structure

void main( ){
  int a;
  int b;
  int c;
  int d;
  int e;
  int f;
  int g;
  e = a - b;
  f = b - c;
  d = a - c;
  g = e + f + 1;
  assert( d <= g );
}
