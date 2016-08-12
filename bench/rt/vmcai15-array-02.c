// Ex Vmcai-array-02.c the example from patric's popl11 paper and used in vmcai 2015

struct mproc{
  int mflag;
  int mparent;
}mproc[24];
void main()
{
  int child;
  int index;
  int who;
  int chindex;
  volatile int parent;
  child = 0;
  mproc[child].mflag = 0;
  child = 1;
  while (child < 24) {
      mproc[child].mflag = 0;
      child = child + 1; }
  child = 23;
  mproc[child].mflag = 99;
  child = 1;
      index = 1;
      if (index < 0)	index = 0;
      if (index > 22)	index = 22;
      who = parent;
      if (who < 0)	who = 0;
      mproc[index].mflag = who;
      child = child + 1;
      index = 21;
      if (index < 0)	index = 0;
      if (index > 22)	index = 22;
      who = parent;
      if (who < 0)	who = 0;
      mproc[index].mflag = who;
      child = child + 1;

  while (child < 23) {
      index = parent;
      if (index < 0)	index = 0;
      if (index > 22)	index = 22;
      who = parent;
      if (who < 0)	who = 0;
      mproc[index].mflag = who;
      child = child + 1; }
  child = 0;
  chindex = 1 ;
      who = parent;
      if (who < 0)
	who = 0;
      mproc[chindex].mflag = who;
      chindex = chindex + 1;
      while(chindex < 24){
	  who = parent;
	  if (who < 0)	    who = 0;
	  mproc[chindex].mflag = who;
	  chindex = chindex + 1;}
      child  = child + 1;
  while(child < 5)  {
      chindex = 1 ;
      who = parent;
      if (who < 0)	
	who = 0;
      mproc[chindex].mflag = who;
      chindex = chindex + 1;
      while(chindex < 24){
	  who = parent;
	  if (who < 0)	    who = 0;
	  mproc[chindex].mflag = who;
	  chindex = chindex + 1;}
      child  = child + 1; }

  who = 4;
  who = mproc[who].mflag;
  assert(who>=0);
}
