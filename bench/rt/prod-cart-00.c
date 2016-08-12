// prod-cart-00.c: only check null pointer satisfy both ill and dll data structure
typedef struct L { // linked list node
  struct H *head ;
  struct L *next ;
  struct L *prev ;
} L;
typedef struct H { // header
  struct L* list;
  int id;
} H;

void main( ){

  H* h;
  L* l_null;
  // initialization  
  h = malloc( 8 );
  l_null = null;

  h->list = null;
  h->id = -1; 

  // checks
  _memcad( "check_inductive( h->list, ill, [ h | | ] )" ) ;
  _memcad( "check_inductive( h->list, dll, [ l_null | | ] )" ) ;
}
