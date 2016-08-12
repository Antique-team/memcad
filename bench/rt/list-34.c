// Ex list-34: list and structures
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list;

typedef struct foo {
  list a;
  list b;
} foo ;

void main( ){
  foo f ;
  list k ;
  {
    list l ;
    _memcad( "add_inductive( l, list )" );
    f.a = l;
    f.b = l;
  }
  f.a = NULL;
  k = f.b;
  _memcad( "check_inductive( k, list )" );
}
