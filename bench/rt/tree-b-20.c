// Ex tree-b-20: tree-b, leftmost path
//    from tree-h-20 and tree-p-20
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  struct etree * p; // parent pointer
  int * h ; // head pointer
  int data ;
} etree ;
typedef etree * tree ;
volatile int cond;
void main( ){
  tree l;
  tree c;
  tree p;
  int * h;
  _memcad( "add_inductive( l, bintreeb_o, [ p, h | | ] )" );
  c = l;
  while( cond ){
    tree c;
    c = l;
    while( cond && c != null ){
      if( cond ){ // insert
        tree m;
        m = malloc( 20 );
	if( m == 0 )
	  exit( 0 );
        m->h = h;
        if( cond ){ // insert left
          m->l = c->l;
          m->r = null;
          m->p = c;
          c->l = m;
          if( m->l != null ){
            m->l->p = m;
          }
        } else { // insert right
          m->l = null;
          m->r = c->r;
          m->p = c;
          c->r = m;
          if( m->r != null ){
            m->r->p = m;
          }
        }
      } else if( cond ){ // go left
        c = c->l;
      } else { // go right
        c = c->r;
      }
    }
    c = null; // to forget c
  }
  _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
}
