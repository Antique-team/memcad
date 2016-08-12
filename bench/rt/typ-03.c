typedef enum {
  T_ERR,
  T_CST,
  T_NEG,
  T_ADD,
  T_MUL,
  //T_SUB,
  //T_DIV
} tag ;

typedef struct arith {
  tag t;
  union {
    struct {
      int value ;
      struct arith * next ;
    } arcst ;
    struct {
      struct arith * ut ;
    } aruni ;
    struct {
      struct arith * bl ;
      struct arith * br ;
    } arbin ;
  } un;
} arith ;

void configure(){
  _spec_assume( "dischargecheckers()" );
  _spec_assume( "newchecker( ~\
def arith(node):\n\
  choose:\n\
    when node->t == 0: % Unknown value\n\
      malloc(node,12) & node != null\n\
    when node->t == 1: % Constant 4 bytes integer\n\
      let value = node->un.arcst.value in\n\
      malloc(node,12) & node != null &\n\
      arith(node->un.arcst.next)\n\
    when node->t == 2: % Negation\n\
      malloc(node,12) & node != null &\n\
      arith(node->un.aruni.ut)\n\
    when node->t == 3: % Addition\n\
      malloc(node,12) & node != null &\n\
      arith(node->un.arbin.bl) & arith(node->un.arbin.br)\n\
    when node->t == 4: % Multiplication\n\
      malloc(node,12) & node != null &\n\
      arith(node->un.arbin.bl) & arith(node->un.arbin.br)\n\
~)");
}

int main(){
  arith * exp;
  arith * c;
  configure();
  _spec_assume("add_edge(kind_C[(exp) =arith=>])");
  c = exp;
  while (c->t != T_ERR)
  {
    if (c->t == T_NEG)
    {
      c = c->un.aruni.ut;
    }
    else if (c->t == T_ADD)
    {
      c = c->un.arbin.bl;
    }
    else if (c->t == T_MUL)
    {
      c = c->un.arbin.bl;
    }
  }
  _spec_assume("merge(0)");
  _spec_assume("print(0)");
  _spec_assume("check_incl( {\
    exp -> 0\
    c -> 3\
    0 -> 1\
    1 =arith()=arith()=> 2\
    2 =arith()=>\
    3 -> 2 } )");
}
