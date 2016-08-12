// Ex shape-less-02:
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
  if( a < 0 ){
    a = 0;
  } else if( a >= 10 ){
    a = 10;
  }
  if( b < 0 ){
    b = 0;
  } else if( b >= 8 ){
    b = 8;
  }
  if( c < 0 ){
    c = 0;
  } else if( c >= 14 ){
    c = 14;
  }
  if( d < 0 ){
    d = 0;
  } else if( d >= 12 ){
    d = 12;
  }
  u = a + b;
  v = c + d;
  res = u + v;
  assert( res >= 0 );
  assert( res <= 44 );
}
