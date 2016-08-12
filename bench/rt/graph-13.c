//graph 13--const definition: add a node 
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
  _memcad( "decl_setvars( E, F, G)" );
  _memcad ("set_assume ( F $sub E )");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  k = malloc( 12 );
  k -> next = l;
  k -> edges = null;
  k -> data = 0;
  l = k;
  k = null; 
  _memcad ("set_assume ( G = l $euplus E )");         
  _memcad( "check_inductive( l, graphc, [ | | F, G] )" );
}
