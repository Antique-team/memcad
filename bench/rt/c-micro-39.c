// EX c-micro-39: pre_post_incr.c
// test that semantic of pre and post ++ is preserved by transformations
void main() {
  int i = 0;
  int j = i++;
  assert(i == 1);
  assert(j == 0);
  ++i;
  assert(i == 2);
}
