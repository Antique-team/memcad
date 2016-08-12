// Ex tree-19: random traversal, and leaf removal
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
  while( cond && c != null ){
    if( cond ){ // traverse, left
      c = c->l;
    } else if( cond ){ // traverse, right
      c = c->r;
    } else if( cond ){
      if( c->l != null ){ // try to remove left leaf
        if( c->l->l == null && c->l->r == null ){
          tree m;
          m = c->l;
          c->l = null;
          free( m );
        }
      }
      // we can join three elements
    } else {
      if( c->r != null ){ // try to remove right leaf
        if( c->r->l == null && c->r->r == null ){
          tree m;
          m = c->r;
          c->r = null;
          free( m );
        }
      }
      // we can join three elements
    }
    // we can join the elements coming from the two previous if statements
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
