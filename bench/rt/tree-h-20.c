// Ex tree-h-20: random tree construction
//    from tree-20
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
  int * p;
  _memcad( "add_inductive( t, bintreeh_o, [ p | | ] )" );
  while( cond ){
    tree c;
    c = t;
    while( cond && c != 0 ){
      if( cond ){ // insert
        tree m;
        m = malloc( 16 );
	if( m == 0 )
	  exit( 0 );
        m->h = p;
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
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
