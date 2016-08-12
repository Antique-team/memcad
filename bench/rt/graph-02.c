//graph 02--const definition: test unfold, inclusion check and join, 
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
void main( ){
  lnode l;
  lnode k;
  _memcad( "decl_setvars( E, F, G )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad ("set_assume ( G = $empty )");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  k = l;
  while( k != 0 ) {
    k = k->next;
  }
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
  // XR: this test is not solved yet!
  //     we need to add a reduction from shapes to set
  // _memcad ("check_inductive( k, graphc, [ | | F, G] )" );
}
