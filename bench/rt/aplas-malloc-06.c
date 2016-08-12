// Ex aplas-malloc-06: building then dropping an element
//    (drop.c)
// Alloc version
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;

void main( ){
  int i;
  list l;
  list fin;
  l = null;
  fin = null;
  i = 0;
  _memcad( "unroll(1)" );
  while( i < 10 ){
    elist *c;
    c = malloc( 8 );
    c->next = null;
    c->data = 99;
    if( fin != null ){
      fin->next = c;
      fin = fin->next;
    } else {
      l = c;
      fin = c;
    }
    i = i + 1;
  }
  // Identifying a first element
  list l1;
  int idx1;
  i = 0;
  l1 = l;
  while( i != idx1 && l1 != fin ){
    l1 = l1 -> next;
    i = i + 1;
  }
  _memcad( "merge()" );
  list pl1;
  pl1 = l;
  // !! current bug:
  //  - r-expr evaluates
  //  - l-value causes two successive unfoldings
  //  - after two unfolding the value computed initially for the r-value
  //    is invalidated
  // => when a member of an expression evaluates and the second causes, unfold,
  //    the first one should be re-evaluated...
  while( pl1->next != l1 ){
    pl1 = pl1->next;
  }
  _memcad( "merge()" );

  // Deleting
  if( fin == l1 ){
    fin = pl1;
  }
  pl1->next = l1->next;
  pl1 = null;
  free( l1 );
  l1 = null;
  _memcad( "merge()" );
  _memcad( "check_inductive( l, list )" );
  _memcad( "force_live(l,fin)" );
}
