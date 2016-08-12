int main(){
  int a;
  int b;
  a = 1;
  b = 2;
  while (a < 7){
    a = a + 1;
    b = b + 1;
  }
  assert(a < b);
}
