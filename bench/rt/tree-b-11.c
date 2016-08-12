// Ex tree-b-11: tree-b, rightmost path
//    from tree-h-11 and tree-p-11
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  struct etree * p; // parent pointer
  int * h ; // head pointer
  int data ;
} etree ;
typedef etree * tree ;
void main( ){
  tree l;
  tree c;
  tree p;
  int * h;
  _memcad( "add_inductive( l, bintreeb_o, [ p, h | | ] )" );
  c = l;
  while( c != 0 ){
    c = c->r;
  }
  _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
}
