// Ex tree-10: tree, leftmost path
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;
void main( ){
  tree l ;
  tree c ;
  _memcad( "add_inductive( l, bintree_o )" );
  c = l;
  while( c != 0 ){
    c = c->l ;
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( l, bintree_o )" );
}
