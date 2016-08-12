// Ex tree-h-14: random traversal, to node
//    from tree-14
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int * h ; // head pointer
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
    if( c != 0 ){
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
