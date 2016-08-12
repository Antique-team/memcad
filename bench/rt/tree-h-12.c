// Ex tree-h-12: tree, random path to leaf
//    from tree-12
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
  while( c != 0 ){
    if( cond ){
      c = c->l;
    } else {
      c = c->r;
    }
  }
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
