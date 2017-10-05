// set-02: set operations
void main( ){
  int a;
  _memcad( "decl_setvars( E, F )" );
  _memcad( "set_assume(E = $empty )" );
  _memcad( "set_assume(F $sub E )" );

  a = a + 1;
  _memcad( "set_check( F = $empty) ");
  _memcad("output_dot(a | SUCC)");
}
