// Ex array-06.c: initialization of an array (2 steps)
typedef struct foo {
  int * p;
  int   i;
} foo;

void main() {
  int i;
  foo t[10];

  i = 0;
  while(i<10) {
    t[i].p = null;
    t[i].i = 24;
    i = i + 1;
  }
  i = i - 1;
}
