// Ex arith-00: leftmost walk, till random point
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
void main( ){
  t a;
  t c;
  int iter;
  _memcad( "add_inductive( a, arith )" );
  iter = 1;
  c = a;
  while( iter == 1 ){
    if( c->tag == 0 ){
      iter = 0;
    } else if( c->tag == 1 ){
      iter = 0;
    } else if( c->tag == 2 ){
      c = c->u.ubin.bl;
    } else {
      iter = 0;
    }
  }
  _memcad( "check_inductive( a, arith )" );
  _memcad( "check_inductive( c, arith )" );
}
