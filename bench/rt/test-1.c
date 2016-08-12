// test-1, test pre analysis
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;
void main( ){
  tree l ;
  tree c ;
  tree tmp;
  tmp = malloc(sizeof (struct etree));
  tmp -> l = null;
  tmp -> r = null;
  int b;
  _memcad( "add_inductive( l, bintree_o )" );
  c = l;
  while( c != 0 ){
    if (b){
      tmp -> l = c-> l;
      c ->l = c->r;
      c -> r = tmp -> l;
    } else {
      tmp -> r = c->r;
      c->r = c->l;
      c->l = tmp -> r;
    }
    c = c->l;
    _memcad( "output_dot( | )" );
    _memcad( "sel_merge ()");
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( l, bintree_o )" );
}
