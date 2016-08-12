// Ex tree-b-21: tree-b, leftmost path
//    from tree-h-21 and tree-p-21
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
  while( l != null ){
    c = l;
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
    _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
  }
}
