//graph 18--const definition: build a graph from empty, 
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
  lnode root = null;
  int i;
  _memcad( "decl_setvars( E, F, G, H )" );
  _memcad ("set_assume ( F $sub E, E = $empty)");
  _memcad( "add_inductive( root, graphc, [ | | F, E] )" );
  /* build a graph and each node has one edge to the next */
  while ( i > 0)
    {
      lnode t = (lnode) malloc ( sizeof(node) );
      t -> next = root;
      t -> data = i;
      if (root != null) {
        t -> edges = (edge *) malloc (sizeof(edge));
        t -> edges -> next = null;
        t -> edges -> dest = root;
      }
      else
        t -> edges = null;
      i = i -1;
      root = t;
    }
   _memcad( "check_inductive( root, graphc, [ | | G, H])" );
   // FBR: some day add (G $sub H) set constraint when we
   //      have the new version of check_inductive ready
}
