// Ex tree-20: random tree construction
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree t;
  _memcad( "add_inductive( t, bintree_o )" );
  //t = malloc( 12 );
  //t->l = null;
  //t->r = null;
  while( cond ){
    tree c;
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
    c = null; // to forget c
  }
  _memcad( "check_inductive( t, bintree_o )" );
}
