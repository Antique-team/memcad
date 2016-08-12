// Ex c-micro-02: address of and deref operators, nested structs
typedef struct str_a {
  int x ;
  int y ;
} str_a ;
typedef struct str_b {
  int u ;
  struct str_a v ;
} str_b ;
void main( ){
  str_b x ;
  str_a * y ;
  x.v.x = 42 ;
  y = &(x.v) ;
  assert( y->x == 42 );
}
