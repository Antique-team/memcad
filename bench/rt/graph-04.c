//graph 04--const definition: unfold one edge 
typedef struct edge {
  struct edge * next ;
  struct node * dest ;
  } edge ;
typedef struct  node {
  struct node * next ;
  struct edge * edges;
  int data;
  } node ;
typedef node * lnode;
typedef edge * ledge;
void main( ){
  lnode l;
  lnode k;
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  k = null;
  if (l != 0)
    { if (l -> edges != 0)
        k = l -> edges -> dest;
      else 
        k = null;
    }
  else
    k = null;
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
}
