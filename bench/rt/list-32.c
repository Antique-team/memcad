// Ex list-32: list traversal
//  was list-traversal.c
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list;

void main( ){
  list l ;
  list k ;
  int data;
  _memcad( "add_inductive( l, list )" );
  k = l;
  while( k != 0 ){
    data = k->data;
    k = k->next;
  }
  _memcad( "check_inductive( l, list )" );
}









