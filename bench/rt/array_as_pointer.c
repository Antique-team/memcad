// TOSORT
// some simple code not handled by memcad
#define TAB_SIZE 2

int main() {

  int tab[TAB_SIZE];

  int zero = 0;
  int one = 1;

  tab[zero] = 0;
  tab[one] = 1;

  assert(0 == *tab);
  assert(1 == *(tab + 1));
}
