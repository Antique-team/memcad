typedef unsigned int U32;


#define spoquelenth 16
#define sporenwunum 4

#define spodormant 1
#define spoready 2
#define sposuspend 3
#define Excuting 4
#define sponull 0
#define sponodeltask 1
#define spoidlerenwu sporenwunum+1
#define spoidlerenwu_id 0xa6


typedef struct {
    U32 id;
    U32 renwuhandler;
    U32 next;
    U32 used;
}sporenwuque;
sporenwuque sporenwuqlie[spoquelenth];
U32 spodormantq_tail = 15;
U32 sporeadyq_tail = 14;
U32 sposuspendq_tail = 13;
U32 spodormantq_head = 0;
U32 sporeadyq_head = 1;
U32 sposuspendq_head = 2;
int spo_qlieinit(sporenwuque renwuqlie[], U32 qliehead, U32 qlietail)
{
    return 0;
}


void main()
{
    U32 i;
    _memcad("aos_start");
    if(i < spoquelenth)
      {
        if(i>=0)
          {
            sporenwuqlie[i].used = 0;
          i = 0;
          sporenwuqlie[i].used = 0;
           i = 1;
          while(i < spoquelenth){
            sporenwuqlie[i].used = 0;
            i = i + 1 ;
          }
          sporenwuqlie[spodormantq_head].id = spoidlerenwu_id;
          sporenwuqlie[spodormantq_head].renwuhandler = spoidlerenwu;
          sporenwuqlie[spodormantq_head].used = 1;
          sporenwuqlie[spodormantq_tail].id = spoidlerenwu_id;
          sporenwuqlie[spodormantq_tail].renwuhandler = spoidlerenwu;
          sporenwuqlie[spodormantq_tail].used = 1;
          sporenwuqlie[spodormantq_head].next = spodormantq_tail;
          sporenwuqlie[spodormantq_tail].next = sponull;
          //In the former version, the assignment on "next" appears before other assgnments which makes
    //the analysis hard

          sporenwuqlie[sporeadyq_head].id = spoidlerenwu_id;
          sporenwuqlie[sporeadyq_head].renwuhandler = spoidlerenwu;
          sporenwuqlie[sporeadyq_head].used = 1;
          sporenwuqlie[sporeadyq_tail].id = spoidlerenwu_id;
          sporenwuqlie[sporeadyq_tail].renwuhandler = spoidlerenwu;
          sporenwuqlie[sporeadyq_tail].used = 1;
          sporenwuqlie[sporeadyq_head].next = sporeadyq_tail;
          sporenwuqlie[sporeadyq_tail].next = sponull;
          
          sporenwuqlie[sposuspendq_head].id = spoidlerenwu_id;
          sporenwuqlie[sposuspendq_head].renwuhandler = spoidlerenwu;
          sporenwuqlie[sposuspendq_head].used = 1;
          sporenwuqlie[sposuspendq_tail].id = spoidlerenwu_id;
          sporenwuqlie[sposuspendq_tail].renwuhandler = spoidlerenwu;
          sporenwuqlie[sposuspendq_tail].used = 1;
          sporenwuqlie[sposuspendq_head].next = sposuspendq_tail;
          sporenwuqlie[sposuspendq_tail].next = sponull;
          _memcad("minix_check");
        }
      }
    return;
}





