// Ex shape-less-08:
//  code manipulating shape-less memory, i.e., no inductive structure

void main( ){
  int a;
  int b;
  int c;
  int * d;
  a = 0;
  b = 2;
  if( c == 1 ){
    d = & a;
  } else {
    d = & b;
  }
  *d = 1;
  // maybe change this assertion
  assert( a < b );
}
