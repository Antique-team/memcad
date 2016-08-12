// Ex next-00: take address of a cell, and use for read/write
void main( )
{
  int x;
  int * y;
  y = & x;
  x = 42;
  assert( *y == 42 );
}
