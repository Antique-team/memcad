// Ex tree-h-19: random traversal, and leaf removal
//    from tree-19
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
  while( cond && c != null ){
    if( cond ){ // traverse, left
      c = c->l;
    } else if( cond ){ // traverse, right
      c = c->r;
    } else if( cond ){
      if( c->l != null ){ // try to remove left leaf
        if( c->l->l == null && c->l->r == null ){
          tree m;
          m = c->l;
          c->l = null;
          free( m );
        }
      }
    } else {
      if( c->r != null ){ // try to remove right leaf
        if( c->r->l == null && c->r->r == null ){
          tree m;
          m = c->r;
          c->r = null;
          free( m );
        }
      }
    }
  }
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
