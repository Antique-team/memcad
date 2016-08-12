// Ex c-micro-60: very simple recursion
int p;
int q;
int r;
void f( ){
  if( r < 0 ){
    p = q;
  } else {
    p = p - 1;
    q = q + 1;
    f( );
  }
}
void main( ){
  f( );
}
