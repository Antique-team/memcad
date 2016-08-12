
typedef struct s {
  int x;
  struct s* ptr;
} s;

void main() {
  s s1, s2, s3;
  s1.x = 3;
  s2.ptr = &s1;
  s3.ptr = &s2;
  assert(s3.ptr->ptr->x == 3); // check struct's type was unfolded two times
}
