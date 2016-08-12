// Ex tree-p-20: random tree construction
//    from tree-20
typedef struct etree {
  struct etree * l;
  struct etree * r;
  struct etree * p; // parent pointer
  int data;
} etree;
typedef etree * tree;
volatile int cond;
void main( ){
  tree t;
  tree p;
  _memcad( "add_inductive( t, bintreep_o, [ p | | ] )" );
  while( cond ){
    tree c;
    c = t;
    while( cond && c != null ){
      if( cond ){ // insert
        tree m;
        m = malloc( 16 );
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
  _memcad( "check_inductive( t, bintreep_o, [ p | | ] )" );
}
