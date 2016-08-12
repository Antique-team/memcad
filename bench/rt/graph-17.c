// Ex, graph-17: const definition, simple graph traversal, non local unfolding

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
  int data;
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  k = l;
  if( k!=0 ){
    ledge g = k->edges;
    if( g != 0 ){
      k = g->dest;
      if( k != 0 ){
        data = k->data;
      }
    }
  }
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
}
