// Ex tree-h-18: random traversal, and leaf removal
//    from tree-18
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
    } else if( c->l != null ){ // try to remove leaf
      if( c->l->l == null && c->l->r == null ){
        tree m;
        m = c->l;
        c->l = null;
        free( m );
      }
    }
  }
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
