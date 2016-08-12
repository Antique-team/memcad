// Ex tree-p-21: iterated leaf removal
//    from tree-21
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
  tree c;
  tree p;
  _memcad( "add_inductive( t, bintreep_o, [ p | | ] )" );
  while( t != null ){
    c = t;
    while( cond && c != 0 ){
      if( cond ){ // go left
        c = c->l;
      } else if( cond ){ // go right
        c = c->r;
      } else if( cond ){
        if( c->l != null ){
          if( c->l->l == null && c->l->r == null ){
            tree m;
            m = c->l;
            c->l = null;
            free( m );
          }
        }
      }
      else if( cond ){
        if( c->r != null ){
          if( c->r->l == null && c->r->r == null ){
            tree m;
            m = c->r;
            c->r = null;
            free( m );
          }
        }
      }
    }
    // _memcad( "check_inductive( c, bintreep_o, [ p | | ] )" );
    _memcad( "check_inductive( t, bintreep_o, [ p | | ] )" );
  }
}
