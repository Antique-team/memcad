// set-06: join over set properties
// should be analyzed without disjunctions (disj_off)
void main( ){
  int a;
  int b;
  _memcad( "decl_setvars( E, F )" );
  if( b ){
     a = a + 1;
    _memcad( "set_assume( E $sub F, a $in E )" );
  } else {
    _memcad( "set_assume( a $in F )" );
  }
  _memcad( "set_check( a $in F )" );
  a = a + 1;
}
