// Ex tree-p-23: tree random swap and rotation
//    from tree-23
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
  c = t;
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
  // _memcad( "check_inductive( c, bintreep_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreep_o, [ p | | ] )" );
}

/* for test selection merge */
void main_e( ){
  tree t;
  tree c;
  tree p;
  _memcad( "add_inductive( t, bintreep_o, [ p | | ] )" );
  c = t;
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
    /* _memcad( "output_dot( c,t,p | SUCC )" ); */
    _memcad( "sel_merge( c,t,p)" );
    /* _memcad( "output_dot( c,t,p | SUCC )" ); */
  }
  // _memcad( "check_inductive( c, bintreep_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreep_o, [ p | | ] )" );
}
