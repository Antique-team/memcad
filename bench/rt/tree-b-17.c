// Ex tree-b-17: tree-b, leftmost path
//    from tree-h-17 and tree-p-17
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
  while( cond && c != 0 ){
    if( cond ){ // go left
      c = c->l;
    } else if( cond ) { // go right
      c = c->r;
    } else if( c->l == null ){
      if( c->r != null ){
        tree m;
        m = c->r;
        c->l = m->l;
        c->r = m->r;
        if( c->l != null ){
          c->l->p = c;
        } // might be good to fold at that point on that if
        if( c->r != null ){
          c->r->p = c;
        }
        free( m );
      }
    }
  }
  _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
}
