// Ex tree-17: random traversal, and node removal
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
    if( c->l == null ){
      if( c->r != null ){
        tree m;
        m = c->r;
        c->l = c->r->l;
        c->r = c->r->r;
        free( m );
      }
    }
    // would be a good point to merge the three disjuncts
    // from the previous if statements
    if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
