// set-01: set decl + assume
void main( ){
  int a;
  _memcad( "decl_setvars( E, F )" );
  _memcad( "set_assume( E $sub F )" );
  _memcad( "set_assume( a $in E )" );
  _memcad( "set_check( a $in F )" );
  a = a + 1;
  _memcad("output_dot(a | SUCC)");
}
