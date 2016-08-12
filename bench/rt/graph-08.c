//graph 08--const definition: a simple graph traversal 
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
  k = l;
  while (k!= 0)
    { if (k -> edges != 0)
        if ( k -> edges -> next != 0) 
          k = k -> edges -> next -> dest;
        else k = k -> edges -> dest;
      else 
        k = null;
    }
  _memcad( "check_inductive( l, graphc, [ | | F, E] )" );
}
