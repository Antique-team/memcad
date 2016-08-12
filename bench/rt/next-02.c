// Ex next-02: structures read and write
typedef struct vect {
  int x;
  int y;
} vect;
void main( )
{
  vect v0;
  vect * v1;
  v1 = & v0;
  v0.x = 8;
  v1->y = 9;
  assert( v1->x == 8 );
  assert( v0.y == 9 );
}
