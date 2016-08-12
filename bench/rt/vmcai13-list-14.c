// dll:
//   . list structure forward tranversal
//   . backward transversal
//   . access to top pointeur

typedef struct _dll {
  struct _dll * next ;
  struct _dll * prev ;
} _dll ;
typedef _dll * dll ;
dll l ;
dll l_null ;
dll l_start ;
dll l_mid ;
void main( ){
  int res;
  l_null = null;
  l = l_start;
  _memcad( "add_inductive( l_start, dllo, [ l_null | | ] )" );
  {
    volatile int rand;
    while( l != null && rand ){
      l = l->next;
    }
  }
  l_mid = l;
  if( l != null ){
    volatile int rand;
    dll c;
    _memcad( "unroll( 1 )" );
    while( l != l_start && rand ){
      c = l;
      l = l->prev;
    }
    _memcad( "force_live( l_mid )" );
  }
}
