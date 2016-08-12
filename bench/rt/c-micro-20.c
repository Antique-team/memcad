// Ex c-micro-20: malloc and join with folding
// - malloc
// - join, with unfolding rule
// -> disjunction domain turned off, in order to force the join
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  list m;
  int b;
  _memcad( "add_inductive( l, list )" );
  if( b ){
    m = l;
  } else {
    m = malloc( 8 );
    m->next = l;
    m->data = 0;
    l = m;
  }
  _memcad( "check_inductive( l, list )" );
}
