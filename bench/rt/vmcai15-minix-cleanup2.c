// Ex Vmcai-minix-exit. The rewritten function of exit in Minix
struct mproc{
  int mflag;
  int mparent;
}mproc[24];
void main()
{
  int child;
  int index;
  int chindex;
  int proc_in_use;
  _memcad("minix_start");
      if (child <  24)
        if (child > 2)
          if(mproc[child].mflag > 0)
            {
              mproc[child].mflag = 0;
              if(index < 24)
                if(index > 2)
                  if(mproc[index].mflag > 0)
                    {
                      mproc[index].mflag = 0;
                      chindex = 0;
                      if( mproc[chindex].mflag > 0)
                        {
                        if (mproc[chindex].mparent == child)
                          {
                            mproc[chindex].mparent = 2;
                          }
                        }
                      chindex = chindex + 1;
                      while( chindex < 24)
                        {
                        if( mproc[chindex].mflag > 0)
                          {
                            if (mproc[chindex].mparent == child)
                              {
                                mproc[chindex].mparent = 2;
                              }
                          }
                        chindex = chindex + 1;
                        }
                      chindex = 0;
                      if( mproc[chindex].mflag > 0)
                        {
                          if (mproc[chindex].mparent == index)
                            {
                            mproc[chindex].mparent = 2;
                            }
                        }
                      chindex = chindex + 1;
                      while( chindex < 24)
                        {
                          if( mproc[chindex].mflag > 0)
                            {
                              if (mproc[chindex].mparent == index)
                                {
                                  mproc[chindex].mparent = 2;
                                }
                            }
                          chindex = chindex + 1;
                        }
                      proc_in_use = proc_in_use - 2;                      
                    _memcad("minix_check");
                    }
            } 
  return;
}
