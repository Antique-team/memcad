// Ex mc-com-03: list reversal
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ) {
  list l ;
  list r ;
  list k ;
  _memcad( "add_inductive( l, list )" );
  r = null;
  _memcad( "add_inductive( r, list )" );
  while( l != 0 ){
    k = l->next;
    l->next = r;
    r = l;
    l = k;
  }
  _memcad( "check_inductive( l, list )" );

  // graph with successors of 'l'
  /* _memcad( "output_dot( l | SUCC )"); */
  // graph with successors of 'l' and "cut leaves"
  /* _memcad( "output_dot( l | SUCC, CUTL )"); */
  // other examples for this memcad command
  /* // graph with the connected component containing 'l' */
  /* _memcad( "output_dot( l | CC )"); */
  // graph with everything
  _memcad( "output_dot( | )");
}
