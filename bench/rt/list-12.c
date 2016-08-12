// Ex list-12: free of a complete list
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  _memcad( "add_inductive( l, list )" );
  while( l != null ){
    list p;
    p = l->next ;
    free( l );
    l = p;
  }
  assert( l == null );
  _memcad( "check_inductive( l, list )" );
}
