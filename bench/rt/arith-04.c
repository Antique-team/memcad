// Ex arith-04: random walk + copy + assert
// Tags:
// 0: constant
// 1: variable
// 2: binary operator
typedef struct arith {
  int tag;
  union {
    struct {
      int value;
    } uconst;
    struct {
      int var;
    } uvar;
    struct {
      int op;
      struct arith * bl;
      struct arith * br;
    } ubin ;
  } u;
} arith ;
typedef arith * t;
void f( t x ){
  t r;
  t c;
  volatile int direct;
  int iter;
  // search of a leaf
  c = x;
  iter = 1;
  while( iter == 1 ){
    if( c->tag == 2 ){
      if( c->u.ubin.bl->tag == 0 ){
        if( c->u.ubin.br->tag == 0 ){
          int r;
          r = c->u.ubin.bl->u.uconst.value + c->u.ubin.br->u.uconst.value;
          free( c->u.ubin.bl );
          free( c->u.ubin.br );
          c->tag = 0;
          c->u.uconst.value = r;
          iter = 0;
        } else {
          c = c->u.ubin.br;
        }
      } else {
        c = c->u.ubin.bl;
      }
    } else {
      iter = 0;
    }
  }
}

void main( ){
  t a;
  _memcad( "add_inductive( a, arith )" );
  f( a );
  _memcad( "check_inductive( a, arith )" );
}
