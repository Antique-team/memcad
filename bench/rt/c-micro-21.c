// Ex c-micro-21: join, with a folding
// - in this case, we force an unfolding followed with a folding back
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
  if( l == null ){
    m = l;
    m = null;
  } else {
    m = l->next;
    m = null;
  }
  _memcad( "check_inductive( l, list )" );
}
