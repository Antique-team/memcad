//graph 01--const definition: test unfold, inclusion check and join, 
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
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, graphc, [ | | F, E] )" );
  k = null;
  if (l!= 0)
    k = l->next;
  else
    k = l;
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
  // FBR: TODO
  // Huisong's proposal to have a more generic check_inductive with a list of 
  // numerical constraints and a list of set constraints
  /* _memcad( "check_inductive( l, graphc, [ | | F, E], [ l != 0 ], [ F $sub E ] ) " ); */
}
