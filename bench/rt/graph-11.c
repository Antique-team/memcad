//graph 11--const definition: add an edge 
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
  ledge g;
  _memcad( "decl_setvars( E, F)" );
  _memcad ("set_assume ( F $sub E, k $in F, k $in E)");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  if (l != 0 && k != 0) {
    g = l -> edges;
    ledge e = malloc (8);
    e -> next = g;
    e -> dest = k;
    l -> edges = e;
  }            
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
}
