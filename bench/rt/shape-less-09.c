// Ex shape-less-09:
//  code manipulating shape-less memory, i.e., no inductive structure

void main( ){
  int a;
  int b;
  int * p;
  int * q;
  a = 0;
  b = 2;
  p = & a;
  q = & b;
  *q = 8;
  p = q;
  a = *p;
  assert( a == b );
}
