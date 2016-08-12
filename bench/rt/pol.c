void main(){
  int x,y,z;
  x = 1;
  y = 2;
  z = 1;
  while (z < 100){
    x = x + y;
    y = y + x;
    z = z + 1;
  }
  assert(x < y);
}
