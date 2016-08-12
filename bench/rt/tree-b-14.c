// Ex tree-b-14: tree-b, leftmost path
//    from tree-h-14 and tree-p-14
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  struct etree * p; // parent pointer
  int * h ; // head pointer
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree l;
  tree c;
  tree p;
  int * h;
  _memcad( "add_inductive( l, bintreeb_o, [ p, h | | ] )" );
  c = l;
  while( cond ){
    if( c != 0 ){
      if( cond ){
        c = c->l;
      } else {
        c = c->r;
      }
    }
  }
  _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
}
