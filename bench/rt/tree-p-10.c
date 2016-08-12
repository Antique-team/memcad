// Ex tree-p-10: tree, leftmost path
//    from tree-10
typedef struct etree {
  struct etree * l;
  struct etree * r;
  struct etree * p; // parent pointer
  int data;
} etree;
typedef etree * tree ;
void main( ){
  tree l;
  tree c;
  tree p;
  _memcad( "add_inductive( l, bintreep_o, [ p | | ] )" );
  c = l;
  while( c != 0 ){
    c = c->l;
  }
  //_memcad( "check_inductive( c, bintreep_o )" );
  _memcad( "check_inductive( l, bintreep_o, [ p | | ] )" );
}
