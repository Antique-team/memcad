// Ex c-micro-90: list traversal with a memory leak
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list c ;
  _memcad( "add_inductive( l, list )" );
  while( l != 0 ){
    l = l->next ;
  }
}
