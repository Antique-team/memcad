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
