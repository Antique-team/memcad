// Ex shape-less-04:
//  code manipulating shape-less memory, i.e., no inductive structure

// TODO: add thresholds

void main( ){
  int i;
  i = 0;
  while( i != -10 ){
    i = i + 1;
    if( i >= 9999 ){
      i = -i;
    }
    assert( i < 10000 );
    assert( i >= -10000 );
  }
  assert( i == -10 );
}
