// Ex list-35: tricky edge update issues
typedef struct test {
  int * a ;
  int * b ;
} test ;
void main( ){
  test t ;
  int  i = 0 ;
  t.b = t.a;
  t.a = NULL;
  t.a = & i;
  t.b = t.a;
  t.a = NULL;
  i = 1;
}
