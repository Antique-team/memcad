// Ex c-micro-06: while loop counter
// the list plays no role whatsoever in this example
// => it tests the "standard" rules on inductive definitions
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  int k ;
  k = 0 ;
  _memcad( "add_inductive( l, list )" );
  while( k < 10 ){
    k = k + 1;
  }
  assert ( k <= 10 );
}
