// Ex tree-23: tree random swap and rotation
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
    }
    // random rotate right to left
    else if( cond && c->r != null ){
      tree m;
      m    = c->r;
      c->r = m->r;
      m->r = m->l;
      m->l = c->l;
      c->l = m;
    }
    // traversal
    else if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
    /* _memcad( "output_dot( c,t,p | SUCC )" ); */
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}

/* for selection merge */
void main_e( ){
  tree t;
  tree c;
  _memcad( "add_inductive( t, bintree_o )" );
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
    }
    // random rotate right to left
    else if( cond && c->r != null ){
      tree m;
      m    = c->r;
      c->r = m->r;
      m->r = m->l;
      m->l = c->l;
      c->l = m;
    }
    // traversal
    else if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
    _memcad( "sel_merge( c,t)" );
    /* _memcad( "output_dot( c,t,p | SUCC )" ); */
  }
  _memcad( "check_inductive( c, bintree_o )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
