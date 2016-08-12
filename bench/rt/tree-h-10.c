// Ex tree-h-10: tree-h, leftmost path
//    from tree-10
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int * h ; // head pointer
  int data ;
} etree ;
typedef etree * tree ;
void main( ){
  tree l ;
  tree c ;
  int * p ;
  _memcad( "add_inductive( l, bintreeh_o, [ p | | ] )" );
  c = l;
  while( c != 0 ){
    c = c->l ;
  }
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( l, bintreeh_o, [ p | | ] )" );
}
