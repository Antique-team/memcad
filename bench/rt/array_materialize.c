int array[100];
int main(){
  int x = 9;
  if( array[x] < 0)
    array[x] = 0;
  x = array[x];
  assert(x >= 0);
  return 0;
}
