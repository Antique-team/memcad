// Ex c-micro-01: address of and deref operators
typedef struct vect
 {
  int x ;
  int y ;
} vect ;

void main( ){
  vect a ;
  vect b ;
  vect * p ;
  p = &a ;
  b.x = 1 ;
  a.y = b.x ;
  p->x = b.x ;
  assert( p->x == 1 );
  assert( a.y == 1 );
}
