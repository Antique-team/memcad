// Ex tree-b-23: tree-b, leftmost path
//    from tree-h-23 and tree-p-23
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
    // random swap
    if( cond ){
      tree m;
      m    = c->r;
      c->r = c->l;
      c->l = m;
    }
    // random rotate left to right
    else if( cond && c->l != null ){
      tree m;
      m    = c->l;
      c->l = m->l;
      m->l = m->r;
      m->r = c->r;
      c->r = m;
      if( c->l != null ){
        c->l->p = c;
      }
      if( m->r != null ){
        m->r->p = m;
      }
    }
    // random rotate right to left
    else if( cond && c->r != null ){
      tree m;
      m    = c->r;
      c->r = m->r;
      m->r = m->l;
      m->l = c->l;
      c->l = m;
      if( c->r != null ){
        c->r->p = c;
      }
      if( m->l != null ){
        m->l->p = m;
      }
    }
    // traversal
    else if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
  }
  _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
}


/* for selection merge */
void main_e( ){
  tree l;
  tree c;
  tree p;
  int * h;
  _memcad( "add_inductive( l, bintreeb_o, [ p, h | | ] )" );
  c = l;
  while( cond && c != 0 ){
    // random swap
    if( cond ){
      tree m;
      m    = c->r;
      c->r = c->l;
      c->l = m;
    }
    // random rotate left to right
    else if( cond && c->l != null ){
      tree m;
      m    = c->l;
      c->l = m->l;
      m->l = m->r;
      m->r = c->r;
      c->r = m;
      if( c->l != null ){
        c->l->p = c;
      }
      if( m->r != null ){
        m->r->p = m;
      }
    }
    // random rotate right to left
    else if( cond && c->r != null ){
      tree m;
      m    = c->r;
      c->r = m->r;
      m->r = m->l;
      m->l = c->l;
      c->l = m;
      if( c->r != null ){
        c->r->p = c;
      }
      if( m->l != null ){
        m->l->p = m;
      }
    }
    // traversal
    else if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
    /* _memcad( "output_dot( c,p,h,l | SUCC )" ); */
    _memcad( "sel_merge( c,p, h, l)" );
    /* _memcad( "output_dot( c,p,h,l | SUCC )" ); */
  }
  _memcad( "check_inductive( l, bintreeb_o, [ p, h | | ] )" );
}
