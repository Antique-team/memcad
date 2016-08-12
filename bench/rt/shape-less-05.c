// Ex shape-less-05:
//  code manipulating shape-less memory, i.e., no inductive structure

void main( ){
  int i;
  i = 0;
  while( i != -10 ){
    i = i + 1;
    if( i >= 10000 ){
      i = 0-i;
    }
    assert( i < 10000 );
    assert( i >= -10000 );
  }
  assert( i == -10 );
}
