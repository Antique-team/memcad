// Ex-53 (union.c): small example of union manipulation

typedef union {
  int i;
  char c;
} u;

void main() {
  u u1;
  u u2;
  u1.i = 1;
  u2.c = 'a';
  assert(u1.i == 1);
  assert(u2.c == 'a');
}
