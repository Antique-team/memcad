// Ex tree-18: random traversal, and leaf removal
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
    if( c->l != null ){
      if( c->l->l == null && c->l->r == null ){
        tree m;
        m = c->l;
        c->l = null;
        free( m );
      }
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
