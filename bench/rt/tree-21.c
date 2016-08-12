// Ex tree-21: iterated leaf removal
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
    _memcad( "check_inductive( c, bintree_o )" );
    _memcad( "check_inductive( t, bintree_o )" );
  }
}

void main_e( ){
  tree t;
  tree c;
  _memcad( "add_inductive( t, bintree_o )" );
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
      /* _memcad( "output_dot(c,t| SUCC  )"); */
      _memcad( "sel_merge()" );
      /* _memcad( "output_dot(c,t| SUCC  )"); */
    }
    _memcad( "check_inductive( c, bintree_o )" );
    _memcad( "check_inductive( t, bintree_o )" );
  }
}
