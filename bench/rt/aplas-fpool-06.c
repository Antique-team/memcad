// Ex drop.c: building then dropping an element
// Array version
// #include "assert.h"
// #include "memcad.h"
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  list l;
  list fin;
  elist t[10];
  l = null;
  fin = null;
  i = 0;
  _memcad( "unroll(1)" );
  while( i < 10 ){
    t[i].next = null;
    t[i].data = 99;
    if (fin != null) {
      fin->next = &t[i];
      fin = fin->next;
    }
    else {
      l = &t[i];
      fin = &t[i];
    }
    i = i + 1;
  }
  // Identifying a first element
  list l1;
  int idx1;
  i = 0;
  l1 = l;
  while( i != idx1 && l1 != fin ) {
    l1 = l1 -> next;
    i = i + 1;
  }
  _memcad( "merge()" );
  list pl1;
  pl1 = l;
  _memcad( "unroll(1)" ); // some unfolding parameters needs to be used here
  while(pl1->next != l1){
    pl1 = pl1->next;
  }
  _memcad( "merge()" );

  // Deleting
  if (fin == l1) fin = pl1;
  pl1->next = l1->next;
  pl1 = null;
  l1 = null;
  _memcad( "merge()" );
  _memcad( "check_inductive( l, list )");
  _memcad( "force_live(l,fin)" );
}

// It seems that:
//  - the invariant at line 45 is faithful
//  - disjunct 0, at 46, after one iteration in the loop presents an
//    incorrect order of the pointers in the structure; it should be
//    pruned away before that (this is what should be investigated).
