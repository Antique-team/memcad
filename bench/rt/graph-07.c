//graph 07--union definition: test unfold, inclusion check and join, 
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
  _memcad( "decl_setvars( E, F)" );
  _memcad ("set_assume ( F $sub E)");
  _memcad( "add_inductive( l, graphu, [ | | F, E] )" );
  k = l;
  while (k!= 0)
    {
      k = k->next;
    }
  _memcad( "check_inductive( l, graphu, [ | | F, E] )" );
}
