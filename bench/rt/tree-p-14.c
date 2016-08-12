// Ex tree-p-14: random traversal, to node
//    from tree-14
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  struct etree * p ; // parent pointer
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree t;
  tree c;
  tree p;
  _memcad( "add_inductive( t, bintreep_o, [ p | | ] )" );
  c = t;
  while( cond ){
    if( c != 0 ){
      if( cond ){
        c = c->l;
      } else {
        c = c->r;
      }
    }
  }
  // _memcad( "check_inductive( c, bintreep_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreep_o, [ p | | ] )" );
}
