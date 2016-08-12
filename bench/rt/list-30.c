// Ex list-30: double list traversal, force_live command
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l0;  // list that gets created first
  list l1;  // cursor 1
  list l2;  // cursor 2
  list tmp; // temporary
  volatile int b;
  // first element creation
  l0 = malloc( 8 );
  l0->next = null;
  l0->data = 24;
  // creation of an arbitrary number of elements
  while( b ){
    tmp = malloc( 8 );
    tmp->next = l0;
    tmp->data = 42;
    l0 = tmp;
  }
  // first cursor arbitrary traversal
  l1 = l0;
  while( b ){
    if( l1 != null ){
      l1 = l1->next;
    }
  }
  // second cursor arbitrary traversal
  l2 = l0;
  while( b ){
    if( l2 != null ){
      l2 = l2->next;
    }
  }
 // _memcad( "force_live( l1 )" );
  _memcad( "check_inductive( l0, list )" );
  // the line below causes a failure earlier in the analysis
  // most likely, due to the pre-analysis
  // _memcad( "check_inductive( l1, list )" );
  _memcad( "check_inductive( l2, list )" );

  // assert( ln == k );
  //  if( ln == k ){
    // hack to check the empty segment was generated
  //  _memcad( "check_bottomness( false )" );
  //}
  //m = ln->next;
  //_memcad( "unfold( m )" );
  //_memcad( "check_bottomness( false )" );
  //_memcad( "force_live( l, ln, k )" );
  //_memcad( "check_inductive( l, list )" );
}
