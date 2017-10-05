// Ex dll-04: dll reverse, with global variables
typedef struct _hdll {
  struct _hdll * next ;
  struct _hdll * prev ;
  int* head;
} _hdll ;
typedef _hdll * hdll ;
int * x;
hdll l ;
hdll k ;
hdll p ;
void main( ){
  x = malloc( 4 );
  if( x == 0 )
    exit( 0 );
  *x = 42;
  k = null;
  l = p;
  _memcad( "add_inductive( l, hdll, [ k, x | | ] )" );
  if( l == null ){
    *x=3;
  } else {
    while( l->next != 0 ){
      l = l->next;
    }
    l=l->prev;
    if( l != null )
      * l->head = 3;
  }
  //_memcad( "unfold( l )" ); // needed to help the next line
  //_memcad( "check_inductive( p, hdll, [ k, x | | ] )" );
}
