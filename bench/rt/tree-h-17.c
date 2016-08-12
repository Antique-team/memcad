// Ex tree-h-17: random traversal, and node removal
//    from tree-17
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
  while( cond && c != 0 ){
    if( c->l == null ){
      if( c->r != null ){
        tree m;
        m = c->r;
        c->l = c->r->l;
        c->r = c->r->r;
        free( m );
      }
    }
    if( cond ){ // go left
      c = c->l;
    } else { // go right
      c = c->r;
    }
  }
  _memcad( "check_inductive( c, bintreeh_o, [ p | | ] )" );
  _memcad( "check_inductive( t, bintreeh_o, [ p | | ] )" );
}
