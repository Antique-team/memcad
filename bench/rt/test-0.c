// test-0:
int com (int i, int j){
  return (i-j);
}

void main( ){
  int a;
  int b;
  while (1){
    if (com(a, b)){
      break;
    }
  }
  _memcad( "sel_merge()" );
}
