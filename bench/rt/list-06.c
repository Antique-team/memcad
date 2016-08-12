// Ex list-06: free of a list node
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  _memcad( "add_inductive( l, list )" );
  if( l != null ){
    list p;
    p = l->next ;
    free( l );
    l = p;
  }
  _memcad( "check_inductive( l, list )" );
}
