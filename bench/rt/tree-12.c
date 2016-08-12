// Ex tree-12: tree, random path to leaf
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree t;
  tree c;
  _memcad( "add_inductive( t, bintree_o )" );
  c = t;
  while( c != 0 ){
    if( cond ){
      c = c->l;
    } else {
      c = c->r;
    }
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
