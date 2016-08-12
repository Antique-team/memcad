// graph 14: delete an edge 
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
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  if (l != 0)
    {
      if (l -> edges != 0)
        l -> edges = l -> edges -> next;
    }
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
}
