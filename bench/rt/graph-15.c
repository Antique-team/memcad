// graph 15--const definition: visit all edges of a node with non-local 
//unfolding 
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
  ledge k;
  lnode dest;
  int data;
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  k = null;
  if (l != 0){
    k = l -> edges;
    while ( k != 0){
      dest = k -> dest;
      if (dest != 0){
        data = dest -> data;
      }
      k = k-> next;
    }
  } else {
    k = null;
  }
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
}
