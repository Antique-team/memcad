// prod-cart-01.c: check data structure of length exactly one.
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
  // initialization  
  h = malloc( 8 );
  l_null = null;

  h->id = -1;
  h->list = malloc( 12 );

  h->list->head = h;
  h->list->next = null;
  h->list->prev = l_null;
  
  // checks
  _memcad( "check_inductive( h->list, ill, [ h | | ] )" ) ;
  _memcad( "check_inductive( h->list, dll, [ l_null | | ] )" ) ;

}
