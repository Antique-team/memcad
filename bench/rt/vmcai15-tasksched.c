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
void main()
{
       U32 ready_first,cur,pre,next,spoexecutnode,renwuheir,curhandler;
       _memcad("aos_start");
       ready_first = sporenwuqlie[sporeadyq_head].next;
       renwuheir = sporenwuqlie[ready_first].renwuhandler;
       spoexecutnode = 5;
      if(sporenwuqlie[spoexecutnode].used ==1 ){
       if(renwuheir > 3){   
         if(renwuheir > 4 ){
            pre = sporeadyq_head;
            next = sporenwuqlie[sporeadyq_head].next;
            cur = sporenwuqlie[sporeadyq_head].next;
            curhandler = sporenwuqlie[cur].renwuhandler;
            while(renwuheir > 6){
               pre = cur;
               next = sporenwuqlie[cur].next;
               cur = sporenwuqlie[cur].next;
               curhandler = sporenwuqlie[cur].renwuhandler;
            }
            sporenwuqlie[pre].next = spoexecutnode;
            sporenwuqlie[spoexecutnode].next = next;
         }
         spoexecutnode = ready_first;
       if(renwuheir > 7){
         pre = sporeadyq_head;
         sporenwuqlie[pre].next = sporenwuqlie[spoexecutnode].next;
       }
     }
     _memcad("minix_check");
   }
return ;
}
