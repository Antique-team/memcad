// set-05: set decl + assume
void main( ){
  int a;
  int * b = &a;
  _memcad( "decl_setvars( E, F )" );
  _memcad( "set_assume( E $sub F )" );
  _memcad( "set_assume( b $in E )" );
  a = a + 1;
  _memcad ( "set_check ( b $in F)" );
  _memcad("output_dot(a | SUCC)");
}
