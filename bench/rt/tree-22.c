// Ex tree-22: tree random swap
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree t;
  tree c;
  _memcad( "add_inductive( t, bintree_o )" );
  c = t;
  while( cond && c != 0 ){
    // random swap
    if( cond ){
      tree m;
      m    = c->r;
      c->r = c->l;
      c->l = m;
    }
    if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
