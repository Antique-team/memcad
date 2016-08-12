// Ex list-00: repeated fold/unfold with no segment
// In this example, the list gets unfolded and then folded back
// => it tests the unfolding and the "unfold" folding rule
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list c ;
  int k ;
  k = 0 ;
  _memcad( "add_inductive( l, list )" );
  while( k < 10 ){
    k = k + 1;
    if( l != null )
      c = l->next ;
    else
      c = null ;
    c = null ;
  }
  assert( k <= 10 );
  _memcad( "check_inductive( l, list )" );
}
