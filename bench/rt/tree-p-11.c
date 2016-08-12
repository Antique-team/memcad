// Ex tree-p-11: tree, rightmost path
//    from tree-11
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  struct etree * p ;
  int data ;
} etree ;
typedef etree * tree ;
void main( ){
  tree l ;
  tree c ;
  tree p ;
  _memcad( "add_inductive( l, bintreep_o, [ p | | ] )" );
  c = l;
  while( c != 0 ){
    c = c->r ;
  }
  //_memcad( "check_inductive( c, bintreep_o, [ p | | ] )" );
  _memcad( "check_inductive( l, bintreep_o, [ p | | ] )" );
}
