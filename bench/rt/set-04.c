// set-04: join over set properties
// should be analyzed without disjunctions (disj_off)

void main( ){
  int a;
  _memcad( "decl_setvars( E, F )" );
  if( a ){
  _memcad( "decl_setvars( E, F )" );
    a = 0;
  } else {
  _memcad( "decl_setvars( G, H )" );
    a = a + 1;
  }
  a = a + 1;
  _memcad("output_dot(a | SUCC)");
}
