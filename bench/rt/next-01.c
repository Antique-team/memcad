// Ex next-01: take address of a cell, and use for read/write
void main( )
{
  int x;
  int * y;
  int * z;
  y = & x;
  z = y;
  *z = 24;
  assert( x == 24 );
}
