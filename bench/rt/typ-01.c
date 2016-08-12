typedef struct arith {
  int t;
  union {
    int value ;
    struct arith * next ;
  } un;
} arith ;
