// Ex Vmcai-array-01. An initialization program in vmcai 2015 paper
struct mproc{
  int mflag;
  int mparent;
}mproc[24];
void main()
{
  int child;
  int index;
  int who;
  child = 0;
  mproc[child].mflag = 0;
  child = 1;
  while (child < 24)
    {
      mproc[child].mflag = 0;
      child = child + 1;
    }
  who = 3;
  who = mproc[who].mflag;
  assert(who == 0);
  return;
}
