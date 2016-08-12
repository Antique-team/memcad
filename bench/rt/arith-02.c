// Ex arith-02: random walk + copy
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
t f( t x ){
  t r;
  t c;
  volatile int direct;
  int iter;
  // search of a leaf
  c = x;
  iter = 1;
  while( iter == 1 ){
    if( c->tag == 0 ){
      iter = 0;
    } else if( c->tag == 1 ){
      iter = 0;
    } else if( c->tag == 2 ){
      if( direct < 0 ){
        c = c->u.ubin.bl;
      } else {
        c = c->u.ubin.br;
      }
    }
  }
  // copy
  //assert( c->tag != 2 );
  r = malloc( 16 );
  r->tag = c->tag;
  if( c->tag == 0 ){
    r->u.uconst.value = c->u.uconst.value;
  } else if( c->tag == 1 ){ // should be 1
    r->u.uvar.var = c->u.uvar.var;
  } else if( c->tag == 2 ){
    r->u.ubin.op = c->u.ubin.op;
    r->u.ubin.bl = c->u.ubin.bl;
    r->u.ubin.br = c->u.ubin.br;
  }
  return r;
}
void main( ){
  t a;
  t y;
  _memcad( "add_inductive( a, arith )" );
  y = f( a );
  _memcad( "check_inductive( a, arith )" );
  _memcad( "check_inductive( y, arith )" );
}
