// prod-cart-03.c: build data struct and check it
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
  h->list = null;
  h->id = -1;
  while( rand ){
    // checks that structures are preserved
    _memcad( "check_inductive( h->list, ill, [ h | | ] )" ) ;
    _memcad( "check_inductive( h->list, dll, [ l_null | | ] )" ) ;
    L* l_cur;
    l_cur = malloc( 12 );
    l_cur->head = h;
    l_cur->next = h->list;
    l_cur->prev = l_null;
    if( h->list ){
      h->list->prev=l_cur;     
    }
    h->list=l_cur;
  }
}
