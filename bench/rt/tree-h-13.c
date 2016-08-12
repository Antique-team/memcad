// Ex tree-h-13: random traversal, to node
//    from tree-13
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int * p ; // head pointer
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree t;
  tree c;
  int * p;
  _memcad( "add_inductive( t, bintreeh_o, [ p | | ] )" );
  c = t;
  while( cond ){
    if( c == 0 ){
    } else {
      if( cond ){
        c = c->l;
      } else {
        c = c->r;
      }
    }
  }
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
