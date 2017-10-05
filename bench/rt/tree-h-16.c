// Ex tree-h-16: random traversal, and insertion
//    from tree-16
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
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
