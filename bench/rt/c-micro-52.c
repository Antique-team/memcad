// EX c-micro-52: sizeof.c

typedef struct {
  char a;
  char b;
} two_chars;

void main() {
  assert(sizeof(two_chars) == 2);
}
