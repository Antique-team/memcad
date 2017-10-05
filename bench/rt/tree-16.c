// Ex tree-16: random traversal, and insertion
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
    if( cond ){ // insert
      tree m;
      m = malloc( 12 );
      if( m == 0 )
        exit( 0 );
      if( cond ){ // insert left
        m->l = c->l;
        m->r = null;
        c->l = m;
      } else { // insert right
        m->l = null;
        m->r = c->r;
        c->r = m;
      }
    } else if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
