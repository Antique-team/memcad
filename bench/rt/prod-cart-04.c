// prod-cart-04.c: assume data struct and check it
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
  volatile int rand;
  h=malloc( 8 );
  l_null = null;
  h->id = -1;
  // assume data structs
  _memcad( "add_inductive( h->list, ill, [ h | | ] )" ) ;
  _memcad( "add_inductive( h->list, dll, [ l_null | | ] )" ) ;    
  // checks that structures are preserved
  _memcad( "check_inductive( h->list, ill, [ h | | ] )" ) ;
  _memcad( "check_inductive( h->list, dll, [ l_null | | ] )" ) ;  
}
