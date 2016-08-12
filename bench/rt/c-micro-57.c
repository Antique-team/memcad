// Ex c-micro-57: return and interaction with scopes
int abs( x ){
  int a = 0;
  if( x < 0 ){
    int z = a ;
    z = z - x ;
    return z ;
  } 
  return x ;
}
void main( ){
  int h;
  int j;
  j = abs( h );
  assert( 0 <= j );
}
