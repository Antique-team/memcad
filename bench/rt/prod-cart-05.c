// prod-cart-05.c: assume d.s., traversal, and check d.s. 
typedef struct L { // linked list node
  struct H *head;
  struct L *next;
  struct L *prev;
} L;
typedef struct H { // header
  int id;
  struct L *list;
} H;

void main( ){

  H* h;
  L* l_null;
  L* l;
  volatile int rand;
  h=malloc( 8 );
  l_null = null;
  h->id = -1;
  // assume data structs
  _memcad( "add_inductive( h->list, ill, [ h | | ] )" ) ;
  _memcad( "add_inductive( h->list, dll, [ l_null | | ] )" ) ;    
  // traversal
  l = h->list;
  while( l ){
    l = l->next;
  }
  // checks that structures are preserved
  _memcad( "check_inductive( h->list, ill, [ h | | ] )" ) ;
  _memcad( "check_inductive( h->list, dll, [ l_null | | ] )" ) ;  
}

