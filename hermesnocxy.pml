/***********************************************************************************************************************************************************
* Date : 12 July 2010 
*  Objective: Verify XY routing algorithm, output arbitration logic for 3X3 mesh
*           : Optimize code by using boolean arrays
************************************************************************************************************************************************************/

/* max number of nodes in system */
#define MAX_NODES   9  
#define MAX_ROUTERS   MAX_NODES 

#define MAX_PACKETS 81

/* Router ID initialization */
#define ROUTER_ID_0_x  0   
#define ROUTER_ID_0_y  0   

#define ROUTER_ID_1_x  1 
#define ROUTER_ID_1_y  0 

#define ROUTER_ID_2_x  2 
#define ROUTER_ID_2_y  0 

#define ROUTER_ID_3_x  0 
#define ROUTER_ID_3_y  1 

#define ROUTER_ID_4_x  1 
#define ROUTER_ID_4_y  1 

#define ROUTER_ID_5_x  2 
#define ROUTER_ID_5_y  1 

#define ROUTER_ID_6_x  0 
#define ROUTER_ID_6_y  2 

#define ROUTER_ID_7_x  1 
#define ROUTER_ID_7_y  2 

#define ROUTER_ID_8_x  2 
#define ROUTER_ID_8_y  2 

/* position indices of all read buffers for each router */
#define NODE_BUFF  0
#define NORTH_BUFF 1
#define EAST_BUFF  2
#define WEST_BUFF  3
#define SOUTH_BUFF 4
#define MAX_BUFF   5

/* define arbitration priorities*/
#define EAST_PRIORITY  5
#define WEST_PRIORITY  4
#define NORTH_PRIORITY 3
#define SOUTH_PRIORITY 2
#define NODE_PRIORITY  1

/* marking invalid packet index */
#define INVALID_PACKET_INDEX 91

/* marking invalid router index */
#define INVALID_ROUTER_INDEX 11

typedef packet { 
 
/* valid for 128 source/dest nodes */
   byte dest_index_x;     
   byte dest_index_y;     
   byte pkt_index;
   byte src_index_x;
   byte src_index_y;
   byte payload;     /* range 0-127 */

 };

/* Once packets are initialized, their data remains constant, by making it hidden, you avoid
   it being part of state space. : Help in scaling verification.
*/
hidden packet packet_list[MAX_PACKETS];

/* assuming that at any instance only one instance of any packet is alive */ 
bool cpacket_sent_status[MAX_PACKETS];

/* dual array, is received */
bool cpacket_received_status[MAX_PACKETS];


/* array for storing read buffers for a router, the value indicates the packet index, into packet array */
typedef readbufflist { 
	byte readbuff[MAX_BUFF];
};

readbufflist router_read_buff[MAX_ROUTERS];

typedef writebufflist { 
	byte writebuff[MAX_BUFF];
};

writebufflist router_write_buff[MAX_ROUTERS];

typedef switchbufflist { 
	bool nodebuffreq[MAX_BUFF];
	bool nodebuffack[MAX_BUFF];
	bool westbuffreq[MAX_BUFF];
	bool westbuffack[MAX_BUFF];
	bool eastbuffreq[MAX_BUFF];
	bool eastbuffack[MAX_BUFF];
	bool northbuffreq[MAX_BUFF];
	bool northbuffack[MAX_BUFF];
	bool southbuffreq[MAX_BUFF];
	bool southbuffack[MAX_BUFF];
};

switchbufflist router_switch_buff[MAX_ROUTERS];

typedef arbitrationlist { 
       byte arbitertoken[MAX_BUFF];
}
arbitrationlist router_arbiter_buff[MAX_ROUTERS];


/* Examples:
 router_read_buff[2][NORTH_BUFF] = 5 tells that there is an input available  from north side to router # 2, 
                                            and it corresponds to the packet, packet_list[5] in transmission,
                                            that is packet is of node 5 is available for transmission*/

/* router_read_buff[3][SOUTH_BUFF] = INVALID_PACKET_INDEX tells that the input buffer of the  south side to router # 3 is empty*/

hidden byte router_id_x[MAX_ROUTERS]; 
hidden byte router_id_y[MAX_ROUTERS]; 

hidden  byte ctr;

byte node_packet_index [MAX_ROUTERS];
byte node_dest_id_x [MAX_ROUTERS] ;
byte node_dest_id_y [MAX_ROUTERS] ;

byte west_packet_index [MAX_ROUTERS];
byte west_dest_id_x [MAX_ROUTERS];
byte west_dest_id_y [MAX_ROUTERS];

byte east_packet_index [MAX_ROUTERS];
byte east_dest_id_x [MAX_ROUTERS];
byte east_dest_id_y [MAX_ROUTERS];

byte north_packet_index [MAX_ROUTERS];
byte north_dest_id_x [MAX_ROUTERS];
byte north_dest_id_y [MAX_ROUTERS];

byte south_packet_index [MAX_ROUTERS];
byte south_dest_id_x [MAX_ROUTERS];
byte south_dest_id_y [MAX_ROUTERS];

hidden byte start_packet_index[MAX_ROUTERS];
hidden byte end_packet_index[MAX_ROUTERS];
hidden byte node_index ;
hidden byte node_base_index[MAX_ROUTERS];

byte pktctr ;

proctype router_node ( byte id )
{
   do
   :: 1 ->  /* process runs forever */
     
       /* non-deterministically select whether to process router part or attached node part. */
       if
       :: 1 ->
            /* this is node part */
            /* logic for generating new packet from node index "id"*/
            /* Now the packet index is hard coded to node index */   

            d_step {   /* change to atomic if any of the cond can block */
                if
                  ::node_base_index[id] != INVALID_PACKET_INDEX -> 
                   if
                     ::cpacket_sent_status[node_base_index[id]] == false  -> 
                               cpacket_sent_status[node_base_index[id]] = true;
                               router_read_buff[id].readbuff[NODE_BUFF] = node_base_index[id]; 
                   fi;  

                 /* generate packet 1 */
                 :: node_base_index[id] != INVALID_PACKET_INDEX -> 
                   if
                    :: cpacket_received_status[node_base_index[id]] == true -> 
                            cpacket_received_status[node_base_index[id]] = true; 
                            cpacket_sent_status[node_base_index[id]] = true;
                     /**** Unmask this to keep sending packets in a loop *********/
                     /*  cpacket_sent_status[node_base_index[id]] = false;  cpacket_received_status[node_base_index[id]] = false; */
                     /*  if */
                     /*      :: node_base_index[id] < end_packet_index[id] ->  node_base_index[id] ++;  */
                     /*      :: node_base_index[id] == end_packet_index[id] ->  node_base_index[id+1] = end_packet_index[id]+1;  */
                     /*      :: node_base_index[id] == INVALID_PACKET_INDEX -> node_base_index[id] = INVALID_PACKET_INDEX; */
                     /*  fi; */ 
                  fi;

                :: router_write_buff[id].writebuff[NODE_BUFF] != INVALID_PACKET_INDEX ->

                 /* Set packet received to true */
                 cpacket_received_status[router_write_buff[id].writebuff[NODE_BUFF]] = true; 
                 router_write_buff[id].writebuff[NODE_BUFF] = INVALID_PACKET_INDEX;
                        
                ::skip
                fi;
             }    /* d_setp over */


       :: 1 -> 
           /* this is router part */
           /* logic for reading data and  arbitration */
           /* arbitration is not required as packet index is only circulated in node, which is one byte and it is switched
              synchronously */
           d_step {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
              /* Code for Switch 1*/
             if
             :: router_read_buff[id].readbuff[NODE_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 node_packet_index [id] =  router_read_buff[id].readbuff[NODE_BUFF];

                 /* Get dest id */
                 node_dest_id_x [id] = packet_list[node_packet_index[id]].dest_index_x;
                 node_dest_id_y [id] = packet_list[node_packet_index[id]].dest_index_y;

                 if
                  /* switch east bound if X of destination address is greater than X of current router address*/
                 :: node_dest_id_x[id] > router_id_x[id] && router_write_buff[id].writebuff[EAST_BUFF] == INVALID_PACKET_INDEX ->
                    router_switch_buff[id].nodebuffreq[EAST_BUFF]  = true;
                    if 
                     :: router_switch_buff[id].nodebuffack[EAST_BUFF]  == true -> 
                          router_write_buff[id].writebuff[EAST_BUFF]  = node_packet_index[id]; router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].nodebuffreq[EAST_BUFF]  = false;
                   fi;

                  /* switch west bound if X of destination address is less than X of current router address*/
                 :: node_dest_id_x[id] < router_id_x[id] && router_write_buff[id].writebuff[WEST_BUFF]  == INVALID_PACKET_INDEX ->
                    router_switch_buff[id].nodebuffreq[WEST_BUFF]  = true;
                    if
                      :: router_switch_buff[id].nodebuffack[WEST_BUFF]  == true -> 
                         router_write_buff[id].writebuff[WEST_BUFF]  = node_packet_index[id]; router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX;router_switch_buff[id].nodebuffreq[WEST_BUFF]  = false;
                    fi;

 
                  /*  If X of destination address is equal to X of current router address, check Y Coordinates*/
                 :: node_dest_id_x[id] == router_id_x[id] ->
                    if
                       /* switch south bound if Y of destination address is less than Y of current router address*/
                      :: node_dest_id_y[id] < router_id_y[id] && router_write_buff[id].writebuff[SOUTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].nodebuffreq[SOUTH_BUFF]  = true; 
                         if
                          :: router_switch_buff[id].nodebuffack[SOUTH_BUFF]  == true  ->
                             router_write_buff[id].writebuff[SOUTH_BUFF]  = node_packet_index[id]; router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].nodebuffreq[SOUTH_BUFF]  = false;
                         fi;
 
                       /* switch north bound if Y of destination address is greater than Y of current router address*/
                      :: node_dest_id_y[id] > router_id_y[id] && router_write_buff[id].writebuff[NORTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].nodebuffreq[NORTH_BUFF]  = true;
                         if
                           :: router_switch_buff[id].nodebuffack[NORTH_BUFF]  == true ->
                              router_write_buff[id].writebuff[NORTH_BUFF]  = node_packet_index[id]; router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].nodebuffreq[NORTH_BUFF]  = false;
                         fi;

                     /*  If Y of destination address is equal to Y of current router address, current router is the destination router*/
                    :: node_dest_id_y[id] == router_id_y[id] && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                       router_switch_buff[id].nodebuffreq[NODE_BUFF]  = true;
                        if
                         :: router_switch_buff[id].nodebuffack[NODE_BUFF]  == true -> 
                            router_write_buff[id].writebuff[NODE_BUFF]  = node_packet_index[id]; router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].nodebuffreq[NODE_BUFF]  = false;
                        fi;
             fi;    
             fi;



             :: router_read_buff[id].readbuff[WEST_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 west_packet_index[id] =  router_read_buff[id].readbuff[WEST_BUFF];

                 /* Get dest id */
                 west_dest_id_x[id] = packet_list[west_packet_index[id]].dest_index_x;
                 west_dest_id_y[id] = packet_list[west_packet_index[id]].dest_index_y;
             
                 if
                  /* switch east bound if X of destination address is greater than X of current router address*/
                 :: west_dest_id_x[id] > router_id_x[id] && router_write_buff[id].writebuff[EAST_BUFF]  == INVALID_PACKET_INDEX ->
                    router_switch_buff[id].westbuffreq[EAST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].westbuffack[EAST_BUFF]  == true ->
                       router_write_buff[id].writebuff[EAST_BUFF]  = west_packet_index[id]; router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].westbuffreq[EAST_BUFF]  = false;
                    fi;

                  /* switch west bound if X of destination address is less than X of current router address*/
                 :: west_dest_id_x[id] < router_id_x[id] && router_write_buff[id].writebuff[WEST_BUFF]  == INVALID_PACKET_INDEX ->
                    router_switch_buff[id].westbuffreq[WEST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].westbuffack[WEST_BUFF]  == true;
                        router_write_buff[id].writebuff[WEST_BUFF]  = west_packet_index[id]; router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].westbuffreq[WEST_BUFF]  = false;
                    fi;

                  /*  If X of destination address is equal to X of current router address, check Y Coordinates*/
                 :: west_dest_id_x[id] == router_id_x[id] ->
                    if
                       /* switch south bound if Y of destination address is less than Y of current router address*/
                      :: west_dest_id_y[id] < router_id_y[id] && router_write_buff[id].writebuff[SOUTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].westbuffreq[SOUTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].westbuffack[SOUTH_BUFF]  == true ->
                             router_write_buff[id].writebuff[SOUTH_BUFF]  = west_packet_index[id]; router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].westbuffreq[SOUTH_BUFF]  = false;
                         fi;

                       /* switch north bound if Y of destination address is greater than Y of current router address*/
                      :: west_dest_id_y[id] > router_id_y[id] && router_write_buff[id].writebuff[NORTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].westbuffreq[NORTH_BUFF]  = true; 
                         if
                          :: router_switch_buff[id].westbuffack[NORTH_BUFF]  == true ->
                             router_write_buff[id].writebuff[NORTH_BUFF]  = west_packet_index[id]; router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].westbuffreq[NORTH_BUFF]  = false;
                         fi;

                     /*  If Y of destination address is equal to Y of current router address, current router is the destination router*/
                    :: west_dest_id_y[id] == router_id_y[id] && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                       router_switch_buff[id].westbuffreq[NODE_BUFF]  = true;
                       if
                        :: router_switch_buff[id].westbuffack[NODE_BUFF]  = true -> 
                           router_write_buff[id].writebuff[NODE_BUFF]  = west_packet_index[id]; router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].westbuffreq[NODE_BUFF]  = false;
                       fi;
                 fi;    
             fi;

             

             :: router_read_buff[id].readbuff[EAST_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 east_packet_index[id] =  router_read_buff[id].readbuff[EAST_BUFF];

                 /* Get dest id */
                 east_dest_id_x[id] = packet_list[east_packet_index[id]].dest_index_x;
                 east_dest_id_y[id] = packet_list[east_packet_index[id]].dest_index_y;
             
                 if
                  /* switch east bound if X of destination address is greater than X of current router address*/
                 :: east_dest_id_x[id] > router_id_x[id] && router_write_buff[id].writebuff[EAST_BUFF]  == INVALID_PACKET_INDEX->
                    router_switch_buff[id].eastbuffreq[EAST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].eastbuffack[EAST_BUFF]  = true ->  
                        router_write_buff[id].writebuff[EAST_BUFF]  = east_packet_index[id]; router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].eastbuffreq[EAST_BUFF]  = false;
                    fi; 

                  /* switch west bound if X of destination address is less than X of current router address*/
                 :: east_dest_id_x[id] < router_id_x[id] && router_write_buff[id].writebuff[WEST_BUFF]  == INVALID_PACKET_INDEX->
                    router_switch_buff[id].eastbuffreq[WEST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].eastbuffack[WEST_BUFF]  == true ->  
                        router_write_buff[id].writebuff[WEST_BUFF]  = east_packet_index[id]; router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].eastbuffreq[WEST_BUFF]  = false;
                    fi;

                  /*  If X of destination address is equal to X of current router address, check Y Coordinates*/
                 :: east_dest_id_x[id] == router_id_x[id] ->
                    if
                       /* switch south bound if Y of destination address is less than Y of current router address*/
                      :: east_dest_id_y[id] < router_id_y[id] && router_write_buff[id].writebuff[SOUTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].eastbuffreq[SOUTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].eastbuffack[SOUTH_BUFF]  == true  ->
                             router_write_buff[id].writebuff[SOUTH_BUFF]  = east_packet_index[id]; router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].eastbuffreq[SOUTH_BUFF]  = false;
                         fi;

                       /* switch north bound if Y of destination address is greater than Y of current router address*/
                      :: east_dest_id_y[id] > router_id_y[id] && router_write_buff[id].writebuff[NORTH_BUFF]  == INVALID_PACKET_INDEX  ->
                         router_switch_buff[id].eastbuffreq[NORTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].eastbuffack[NORTH_BUFF]  == true -> 
                             router_write_buff[id].writebuff[NORTH_BUFF]  = east_packet_index[id]; router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].eastbuffreq[NORTH_BUFF]  = false;
                         fi;

                     /*  If Y of destination address is equal to Y of current router address, current router is the destination router*/
                    :: east_dest_id_y[id] == router_id_y[id] && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                       router_switch_buff[id].eastbuffreq[NODE_BUFF]  = true;
                       if
                        :: router_switch_buff[id].eastbuffack[NODE_BUFF]  == true  ->
                           router_write_buff[id].writebuff[NODE_BUFF]  = east_packet_index[id]; router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].eastbuffreq[NODE_BUFF]  = false;
                       fi;
                 fi;    
             fi;
                 
              /* Code for Switch 4*/

             :: router_read_buff[id].readbuff[NORTH_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 north_packet_index[id] =  router_read_buff[id].readbuff[NORTH_BUFF];

                 /* Get dest id */
                 north_dest_id_x[id] = packet_list[north_packet_index[id]].dest_index_x;
                 north_dest_id_y[id] = packet_list[north_packet_index[id]].dest_index_y;
             
                 if
                  /* switch east bound if X of destination address is greater than X of current router address*/
                 :: north_dest_id_x[id] > router_id_x[id] && router_write_buff[id].writebuff[EAST_BUFF]  == INVALID_PACKET_INDEX->
                    router_switch_buff[id].northbuffreq[EAST_BUFF]  = true; 
                    if
                     :: router_switch_buff[id].northbuffack[EAST_BUFF]  == true ->
                        router_write_buff[id].writebuff[EAST_BUFF]  = north_packet_index[id]; router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].northbuffreq[EAST_BUFF]  = false;
                    fi;
 
                  /* switch west bound if X of destination address is less than X of current router address*/
                 :: north_dest_id_x[id] < router_id_x[id] && router_write_buff[id].writebuff[WEST_BUFF]  == INVALID_PACKET_INDEX->
                    router_switch_buff[id].northbuffreq[WEST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].northbuffack[WEST_BUFF]  == true -> 
                        router_write_buff[id].writebuff[WEST_BUFF]  = north_packet_index[id]; router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].northbuffreq[WEST_BUFF]  = false;
                    fi;

                  /*  If X of destination address is equal to X of current router address, check Y Coordinates*/
                 :: north_dest_id_x[id] == router_id_x[id] ->
                    if
                       /* switch south bound if Y of destination address is less than Y of current router address*/
                      :: north_dest_id_y[id] < router_id_y[id] && router_write_buff[id].writebuff[SOUTH_BUFF]  == INVALID_PACKET_INDEX->
                         router_switch_buff[id].northbuffreq[SOUTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].northbuffack[SOUTH_BUFF]  == true ->
                             router_write_buff[id].writebuff[SOUTH_BUFF]  = north_packet_index[id]; router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].northbuffreq[SOUTH_BUFF]  = false;
                          fi;

                       /* switch north bound if Y of destination address is greater than Y of current router address*/
                      :: north_dest_id_y[id] > router_id_y[id] && router_write_buff[id].writebuff[NORTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].northbuffreq[NORTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].northbuffack[NORTH_BUFF]  == true ->
                             router_write_buff[id].writebuff[NORTH_BUFF]  = north_packet_index[id]; router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].northbuffreq[NORTH_BUFF]  = false;
                         fi;

                     /*  If Y of destination address is equal to Y of current router address, current router is the destination router*/
                    :: north_dest_id_y[id] == router_id_y[id] && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                       router_switch_buff[id].northbuffreq[NODE_BUFF]  = true;
                       if
                        :: router_switch_buff[id].northbuffack[NODE_BUFF]  == true ->
                           router_write_buff[id].writebuff[NODE_BUFF]  = north_packet_index[id]; router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].northbuffreq[NODE_BUFF]  = false;
                       fi;
                 fi;    
             fi;


             :: router_read_buff[id].readbuff[SOUTH_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 south_packet_index[id] =  router_read_buff[id].readbuff[SOUTH_BUFF];

                 /* Get dest id */
                 south_dest_id_x[id] = packet_list[south_packet_index[id]].dest_index_x;
                 south_dest_id_y[id] = packet_list[south_packet_index[id]].dest_index_y;
             
                 if
                  /* switch east bound if X of destination address is greater than X of current router address*/
                 :: south_dest_id_x[id] > router_id_x[id] && router_write_buff[id].writebuff[EAST_BUFF]  == INVALID_PACKET_INDEX ->
                    router_switch_buff[id].southbuffreq[EAST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].southbuffack[EAST_BUFF]  == true ->
                        router_write_buff[id].writebuff[EAST_BUFF]  = south_packet_index[id]; router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].southbuffreq[EAST_BUFF]  = false;
                    fi;

                  /* switch west bound if X of destination address is less than X of current router address*/
                 :: south_dest_id_x[id] < router_id_x[id] && router_write_buff[id].writebuff[WEST_BUFF]  == INVALID_PACKET_INDEX ->
                    router_switch_buff[id].southbuffreq[WEST_BUFF]  = true;
                    if
                     :: router_switch_buff[id].southbuffack[WEST_BUFF]  == true ->
                        router_write_buff[id].writebuff[WEST_BUFF]  = south_packet_index[id]; router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].southbuffreq[WEST_BUFF]  = false;
                    fi;

                  /*  If X of destination address is equal to X of current router address, check Y Coordinates*/
                 :: south_dest_id_x[id] == router_id_x[id] ->
                    if
                       /* switch south bound if Y of destination address is less than Y of current router address*/
                      :: south_dest_id_y[id] < router_id_y[id] && router_write_buff[id].writebuff[SOUTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].southbuffreq[SOUTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].southbuffack[SOUTH_BUFF]  == true ->
                             router_write_buff[id].writebuff[SOUTH_BUFF]  = south_packet_index[id]; router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].southbuffreq[SOUTH_BUFF]  = false;
                         fi;

                       /* switch north bound if Y of destination address is greater than Y of current router address*/
                      :: south_dest_id_y[id] > router_id_y[id] && router_write_buff[id].writebuff[NORTH_BUFF]  == INVALID_PACKET_INDEX ->
                         router_switch_buff[id].southbuffreq[NORTH_BUFF]  = true;
                         if
                          :: router_switch_buff[id].southbuffack[NORTH_BUFF]  == true ->
                             router_write_buff[id].writebuff[NORTH_BUFF]  = south_packet_index[id]; router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].southbuffreq[NORTH_BUFF]  = false;
                         fi;

                     /*  If Y of destination address is equal to Y of current router address, current router is the destination router*/
                    :: south_dest_id_y[id] == router_id_y[id] && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                       router_switch_buff[id].southbuffreq[NODE_BUFF]  = true;
                       if
                        :: router_switch_buff[id].southbuffack[NODE_BUFF]  == true ->
                           router_write_buff[id].writebuff[NODE_BUFF]  = south_packet_index[id]; router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX; router_switch_buff[id].southbuffreq[NODE_BUFF]  = false;
                       fi; 
                 fi;    
             fi;

                ::skip

             fi;
        } /* d_setp over */


           /* this is arbiter part */
           /* logic for checking request line */
              /* Priority: East > West > North > South > Node */

       :: 1 -> 
           atomic {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
             if
             :: router_switch_buff[id].eastbuffreq[NODE_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == EAST_PRIORITY ->
                router_switch_buff[id].eastbuffack[NODE_BUFF]  = true;
                if
                 :: router_switch_buff[id].eastbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == EAST_PRIORITY ->
                    router_switch_buff[id].eastbuffack[NODE_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NODE_BUFF] == WEST_PRIORITY;
                fi;
             :: router_switch_buff[id].eastbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == EAST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NODE_BUFF] == WEST_PRIORITY;
             :: router_switch_buff[id].westbuffreq[NODE_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == WEST_PRIORITY ->
                router_switch_buff[id].westbuffack[NODE_BUFF]  = true;
                if
                 :: router_switch_buff[id].westbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == WEST_PRIORITY ->
                    router_switch_buff[id].westbuffack[NODE_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NORTH_PRIORITY;
                fi;
             :: router_switch_buff[id].westbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == WEST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NORTH_PRIORITY;
             :: router_switch_buff[id].northbuffreq[NODE_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NORTH_PRIORITY ->
                router_switch_buff[id].northbuffack[NODE_BUFF]  = true;
                if
                 :: router_switch_buff[id].northbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NORTH_PRIORITY ->
                    router_switch_buff[id].northbuffack[NODE_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NODE_BUFF] == SOUTH_PRIORITY;
                fi;       
             :: router_switch_buff[id].northbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NORTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NODE_BUFF] == SOUTH_PRIORITY;
             :: router_switch_buff[id].southbuffreq[NODE_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == SOUTH_PRIORITY ->
                router_switch_buff[id].southbuffack[NODE_BUFF]  = true;
                if
                 :: router_switch_buff[id].southbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == SOUTH_PRIORITY ->
                    router_switch_buff[id].southbuffack[NODE_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NODE_PRIORITY;
                fi;       
             :: router_switch_buff[id].southbuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == SOUTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NODE_PRIORITY;
             :: router_switch_buff[id].nodebuffreq[NODE_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NODE_PRIORITY ->
                router_switch_buff[id].nodebuffack[NODE_BUFF]  = true;
                if
                 :: router_switch_buff[id].nodebuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NODE_PRIORITY ->
                    router_switch_buff[id].nodebuffack[NODE_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NODE_BUFF] == EAST_PRIORITY;
                fi;       
             :: router_switch_buff[id].nodebuffreq[NODE_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NODE_BUFF] == NODE_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NODE_BUFF] == EAST_PRIORITY;   
             fi;

            }/* d_setp over */



       :: 1 -> 
           atomic {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
             if
             :: router_switch_buff[id].eastbuffreq[WEST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == EAST_PRIORITY ->
                router_switch_buff[id].eastbuffack[WEST_BUFF]  = true;
                if
                 :: router_switch_buff[id].eastbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == EAST_PRIORITY ->
                    router_switch_buff[id].eastbuffack[WEST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[WEST_BUFF] == WEST_PRIORITY;
                fi;
             :: router_switch_buff[id].eastbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == EAST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[WEST_BUFF] == WEST_PRIORITY;
             :: router_switch_buff[id].westbuffreq[WEST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == WEST_PRIORITY ->
                router_switch_buff[id].westbuffack[WEST_BUFF]  = true;
                if
                 :: router_switch_buff[id].westbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == WEST_PRIORITY ->
                    router_switch_buff[id].westbuffack[WEST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NORTH_PRIORITY;
                fi;
             :: router_switch_buff[id].westbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == WEST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NORTH_PRIORITY;
             :: router_switch_buff[id].northbuffreq[WEST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NORTH_PRIORITY ->
                router_switch_buff[id].northbuffack[WEST_BUFF]  = true;
                if
                 :: router_switch_buff[id].northbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NORTH_PRIORITY ->
                    router_switch_buff[id].northbuffack[WEST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[WEST_BUFF] == SOUTH_PRIORITY;
                fi;       
             :: router_switch_buff[id].northbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NORTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[WEST_BUFF] == SOUTH_PRIORITY;
             :: router_switch_buff[id].southbuffreq[WEST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == SOUTH_PRIORITY ->
                router_switch_buff[id].southbuffack[WEST_BUFF]  = true;
                if
                 :: router_switch_buff[id].southbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == SOUTH_PRIORITY ->
                    router_switch_buff[id].southbuffack[WEST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NODE_PRIORITY;
                fi;       
             :: router_switch_buff[id].southbuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == SOUTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NODE_PRIORITY;
             :: router_switch_buff[id].nodebuffreq[WEST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NODE_PRIORITY ->
                router_switch_buff[id].nodebuffack[WEST_BUFF]  = true;
                if
                 :: router_switch_buff[id].nodebuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NODE_PRIORITY ->
                    router_switch_buff[id].nodebuffack[WEST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[WEST_BUFF] == EAST_PRIORITY;
                fi;       
             :: router_switch_buff[id].nodebuffreq[WEST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[WEST_BUFF] == NODE_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[WEST_BUFF] == EAST_PRIORITY;   
             fi;

            }/* d_setp over */




       :: 1 -> 
           atomic {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
             if
             :: router_switch_buff[id].eastbuffreq[EAST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == EAST_PRIORITY ->
                router_switch_buff[id].eastbuffack[EAST_BUFF]  = true;
                if
                 :: router_switch_buff[id].eastbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == EAST_PRIORITY ->
                    router_switch_buff[id].eastbuffack[EAST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[EAST_BUFF] == WEST_PRIORITY;
                fi;
             :: router_switch_buff[id].eastbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == EAST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[EAST_BUFF] == WEST_PRIORITY;
             :: router_switch_buff[id].westbuffreq[EAST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == WEST_PRIORITY ->
                router_switch_buff[id].westbuffack[EAST_BUFF]  = true;
                if
                 :: router_switch_buff[id].westbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == WEST_PRIORITY ->
                    router_switch_buff[id].westbuffack[EAST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NORTH_PRIORITY;
                fi;
             :: router_switch_buff[id].westbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == WEST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NORTH_PRIORITY;
             :: router_switch_buff[id].northbuffreq[EAST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NORTH_PRIORITY ->
                router_switch_buff[id].northbuffack[EAST_BUFF]  = true;
                if
                 :: router_switch_buff[id].northbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NORTH_PRIORITY ->
                    router_switch_buff[id].northbuffack[EAST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[EAST_BUFF] == SOUTH_PRIORITY;
                fi;       
             :: router_switch_buff[id].northbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NORTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[EAST_BUFF] == SOUTH_PRIORITY;
             :: router_switch_buff[id].southbuffreq[EAST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == SOUTH_PRIORITY ->
                router_switch_buff[id].southbuffack[EAST_BUFF]  = true;
                if
                 :: router_switch_buff[id].southbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == SOUTH_PRIORITY ->
                    router_switch_buff[id].southbuffack[EAST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NODE_PRIORITY;
                fi;       
             :: router_switch_buff[id].southbuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == SOUTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NODE_PRIORITY;
             :: router_switch_buff[id].nodebuffreq[EAST_BUFF]  == true && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NODE_PRIORITY ->
                router_switch_buff[id].nodebuffack[EAST_BUFF]  = true;
                if
                 :: router_switch_buff[id].nodebuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NODE_PRIORITY ->
                    router_switch_buff[id].nodebuffack[EAST_BUFF]  = false;router_arbiter_buff[id].arbitertoken[EAST_BUFF] == EAST_PRIORITY;
                fi;       
             :: router_switch_buff[id].nodebuffreq[EAST_BUFF]  == false && router_arbiter_buff[id].arbitertoken[EAST_BUFF] == NODE_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[EAST_BUFF] == EAST_PRIORITY;   
             fi;

            }/* d_setp over */




       :: 1 -> 
           atomic {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
             if
             :: router_switch_buff[id].eastbuffreq[NORTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == EAST_PRIORITY ->
                router_switch_buff[id].eastbuffack[NORTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].eastbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == EAST_PRIORITY ->
                    router_switch_buff[id].eastbuffack[NORTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == WEST_PRIORITY;
                fi;
             :: router_switch_buff[id].eastbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == EAST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == WEST_PRIORITY;
             :: router_switch_buff[id].westbuffreq[NORTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == WEST_PRIORITY ->
                router_switch_buff[id].westbuffack[NORTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].westbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == WEST_PRIORITY ->
                    router_switch_buff[id].westbuffack[NORTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NORTH_PRIORITY;
                fi;
             :: router_switch_buff[id].westbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == WEST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NORTH_PRIORITY;
             :: router_switch_buff[id].northbuffreq[NORTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NORTH_PRIORITY ->
                router_switch_buff[id].northbuffack[NORTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].northbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NORTH_PRIORITY ->
                    router_switch_buff[id].northbuffack[NORTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == SOUTH_PRIORITY;
                fi;       
             :: router_switch_buff[id].northbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NORTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == SOUTH_PRIORITY;
             :: router_switch_buff[id].southbuffreq[NORTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == SOUTH_PRIORITY ->
                router_switch_buff[id].southbuffack[NORTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].southbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == SOUTH_PRIORITY ->
                    router_switch_buff[id].southbuffack[NORTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NODE_PRIORITY;
                fi;       
             :: router_switch_buff[id].southbuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == SOUTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NODE_PRIORITY;
             :: router_switch_buff[id].nodebuffreq[NORTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NODE_PRIORITY ->
                router_switch_buff[id].nodebuffack[NORTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].nodebuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NODE_PRIORITY ->
                    router_switch_buff[id].nodebuffack[NORTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == EAST_PRIORITY;
                fi;       
             :: router_switch_buff[id].nodebuffreq[NORTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == NODE_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[NORTH_BUFF] == EAST_PRIORITY;   
             fi;

            }/* d_setp over */




       :: 1 -> 
           atomic {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
             if
             :: router_switch_buff[id].eastbuffreq[SOUTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == EAST_PRIORITY ->
                router_switch_buff[id].eastbuffack[SOUTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].eastbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == EAST_PRIORITY ->
                    router_switch_buff[id].eastbuffack[SOUTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == WEST_PRIORITY;
                fi;
             :: router_switch_buff[id].eastbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == EAST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == WEST_PRIORITY;
             :: router_switch_buff[id].westbuffreq[SOUTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == WEST_PRIORITY ->
                router_switch_buff[id].westbuffack[SOUTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].westbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == WEST_PRIORITY ->
                    router_switch_buff[id].westbuffack[SOUTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NORTH_PRIORITY;
                fi;
             :: router_switch_buff[id].westbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == WEST_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NORTH_PRIORITY;
             :: router_switch_buff[id].northbuffreq[SOUTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NORTH_PRIORITY ->
                router_switch_buff[id].northbuffack[SOUTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].northbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NORTH_PRIORITY ->
                    router_switch_buff[id].northbuffack[SOUTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == SOUTH_PRIORITY;
                fi;       
             :: router_switch_buff[id].northbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NORTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == SOUTH_PRIORITY;
             :: router_switch_buff[id].southbuffreq[SOUTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == SOUTH_PRIORITY ->
                router_switch_buff[id].southbuffack[SOUTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].southbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == SOUTH_PRIORITY ->
                    router_switch_buff[id].southbuffack[SOUTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NODE_PRIORITY;
                fi;       
             :: router_switch_buff[id].southbuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == SOUTH_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NODE_PRIORITY;
             :: router_switch_buff[id].nodebuffreq[SOUTH_BUFF]  == true && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NODE_PRIORITY ->
                router_switch_buff[id].nodebuffack[SOUTH_BUFF]  = true;
                if
                 :: router_switch_buff[id].nodebuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NODE_PRIORITY ->
                    router_switch_buff[id].nodebuffack[SOUTH_BUFF]  = false;router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == EAST_PRIORITY;
                fi;       
             :: router_switch_buff[id].nodebuffreq[SOUTH_BUFF]  == false && router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == NODE_PRIORITY -> 
                router_arbiter_buff[id].arbitertoken[SOUTH_BUFF] == EAST_PRIORITY;   
             fi;

            }/* d_setp over */


       fi; /* rotuer action over */

   od;   /* top do loop */
}


/*This process initializes packets and starts up the router */
proctype startup () 
{

 /* Intialize packet_list array */ 

    /* Node 0 data */
    /* node 0 has 9 packets */

    /* start_packet_index[0] = INVALID_PACKET_INDEX; */
    start_packet_index[0] = 0;
    end_packet_index[0]   = 8;


   node_index = 0;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 0;
   packet_list[node_index].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 1;
   packet_list[node_index+1].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 2;
   packet_list[node_index+2].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 3;
   packet_list[node_index+3].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 4;
   packet_list[node_index+4].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 5;
   packet_list[node_index+5].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 6;
   packet_list[node_index+6].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 7;
   packet_list[node_index+7].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 8;
   packet_list[node_index+8].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+8].payload=44;   

    /* Node 1 data */
    /* node 1 has 2 packets */

    start_packet_index[1] = INVALID_PACKET_INDEX; 
    /* start_packet_index[1] = 9;*/
    end_packet_index[1]   = 17;


   node_index = 9;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 9;
   packet_list[node_index].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 10;
   packet_list[node_index+1].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 11;
   packet_list[node_index+2].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 12;
   packet_list[node_index+3].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 13;
   packet_list[node_index+4].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 14;
   packet_list[node_index+5].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 15;
   packet_list[node_index+6].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 16;
   packet_list[node_index+7].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 17;
   packet_list[node_index+8].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index+8].payload=44;   

    /* Node 2 data */
    /* node 2 has 2 packets */

    start_packet_index[2] = INVALID_PACKET_INDEX; 
    /* start_packet_index[2] = 18; */
    end_packet_index[2]   = 26;


   node_index = 18;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 18;
   packet_list[node_index].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 19;
   packet_list[node_index+1].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 20;
   packet_list[node_index+2].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 21;
   packet_list[node_index+3].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 22;
   packet_list[node_index+4].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 23;
   packet_list[node_index+5].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 24;
   packet_list[node_index+6].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 25;
   packet_list[node_index+7].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 26;
   packet_list[node_index+8].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index+8].payload=44;   

    /* Node 3 data */
    /* node 3 has 2 packets */


    start_packet_index[3] = INVALID_PACKET_INDEX; 
    /* start_packet_index[3] = 27; */
    end_packet_index[3]   = 35;


   node_index = 27;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 27;
   packet_list[node_index].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 28;
   packet_list[node_index+1].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 29;
   packet_list[node_index+2].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 30;
   packet_list[node_index+3].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 31;
   packet_list[node_index+4].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 32;
   packet_list[node_index+5].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 33;
   packet_list[node_index+6].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 34;
   packet_list[node_index+7].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 35;
   packet_list[node_index+8].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index+8].payload=44;   

    /* Node 4 data */
    /* node 4 has 2 packets */

    start_packet_index[4] = INVALID_PACKET_INDEX; 
    /* start_packet_index[4] = 36; */
    end_packet_index[4]   = 44;


   node_index = 36;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 36;
   packet_list[node_index].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 37;
   packet_list[node_index+1].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 38;
   packet_list[node_index+2].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 39;
   packet_list[node_index+3].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 40;
   packet_list[node_index+4].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 41;
   packet_list[node_index+5].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 42;
   packet_list[node_index+6].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 43;
   packet_list[node_index+7].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 44;
   packet_list[node_index+8].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index+8].payload=44;   

    /* Node 5 data */
    /* node 5 has 2 packets */

    start_packet_index[5] = INVALID_PACKET_INDEX; 
    /* start_packet_index[5] = 45; */
    end_packet_index[5]   = 53;


   node_index = 45;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 45;
   packet_list[node_index].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 46;
   packet_list[node_index+1].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 47;
   packet_list[node_index+2].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 48;
   packet_list[node_index+3].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 49;
   packet_list[node_index+4].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 50;
   packet_list[node_index+5].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 51;
   packet_list[node_index+6].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 52;
   packet_list[node_index+7].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 53;
   packet_list[node_index+8].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index+8].payload=44;   

    /* Node 6 data */
    /* node 6 has 2 packets */

    start_packet_index[6] = INVALID_PACKET_INDEX; 
    /* start_packet_index[6] = 54; */
    end_packet_index[6]   = 62;


   node_index = 54;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 54;
   packet_list[node_index].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 55;
   packet_list[node_index+1].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 56;
   packet_list[node_index+2].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+2].payload=44;   
 
   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 57;
   packet_list[node_index+3].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 58;
   packet_list[node_index+4].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 59;
   packet_list[node_index+5].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 60;
   packet_list[node_index+6].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 61;
   packet_list[node_index+7].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 62;
   packet_list[node_index+8].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index+8].payload=44;   

    /* Node 7 data */
    /* node 7 has 2 packets */

    start_packet_index[7] = INVALID_PACKET_INDEX; 
    /* start_packet_index[7] = 63; */
    end_packet_index[7]   = 71;


   node_index = 63;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 63;
   packet_list[node_index].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index].payload=44;   

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 64;
   packet_list[node_index+1].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 65;
   packet_list[node_index+2].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 66;
   packet_list[node_index+3].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 67;
   packet_list[node_index+4].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 68;
   packet_list[node_index+5].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 69;
   packet_list[node_index+6].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 70;
   packet_list[node_index+7].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 71;
   packet_list[node_index+8].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index+8].payload=44;   

   /* Node 8 data */
    /* node 8 has 2 packets */

    start_packet_index[8] = INVALID_PACKET_INDEX; 
    /* start_packet_index[8] = 72; */
    end_packet_index[8]   = 80;


   node_index = 72;

   packet_list[node_index].dest_index_x = ROUTER_ID_0_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_0_y; 
   packet_list[node_index].pkt_index = 72;
   packet_list[node_index].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index].payload=44;   
   /* Intialize packet_list array, packets at each node */ 

   packet_list[node_index+1].dest_index_x = ROUTER_ID_1_x; 
   packet_list[node_index+1].dest_index_y = ROUTER_ID_1_y; 
   packet_list[node_index+1].pkt_index = 73;
   packet_list[node_index+1].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 74;
   packet_list[node_index+2].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 75;
   packet_list[node_index+3].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 76;
   packet_list[node_index+4].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 77;
   packet_list[node_index+5].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 78;
   packet_list[node_index+6].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 79;
   packet_list[node_index+7].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 80;
   packet_list[node_index+8].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index+8].payload=44;   

 
   /*Initialise router id */
   router_id_x[0] = ROUTER_ID_0_x;  
   router_id_y[0] = ROUTER_ID_0_y;  

   router_id_x[1] = ROUTER_ID_1_x;  
   router_id_y[1] = ROUTER_ID_1_y;  

   router_id_x[2] = ROUTER_ID_2_x;  
   router_id_y[2] = ROUTER_ID_2_y;  

   router_id_x[3] = ROUTER_ID_3_x;  
   router_id_y[3] = ROUTER_ID_3_y;  

   router_id_x[4] = ROUTER_ID_4_x;  
   router_id_y[4] = ROUTER_ID_4_y;  

   router_id_x[5] = ROUTER_ID_5_x;  
   router_id_y[5] = ROUTER_ID_5_y;  

   router_id_x[6] = ROUTER_ID_6_x;  
   router_id_y[6] = ROUTER_ID_6_y;  

   router_id_x[7] = ROUTER_ID_7_x;  
   router_id_y[7] = ROUTER_ID_7_y;  

   router_id_x[8] = ROUTER_ID_8_x;  
   router_id_y[8] = ROUTER_ID_8_y;  
  
    ctr = 0; /* declared at top */

  atomic{
   do 
   :: ctr < MAX_NODES ->
      run router_node( ctr );
      router_read_buff[ctr].readbuff[NODE_BUFF]= INVALID_PACKET_INDEX;
      router_read_buff[ctr].readbuff[NORTH_BUFF]= INVALID_PACKET_INDEX;
      router_read_buff[ctr].readbuff[SOUTH_BUFF]= INVALID_PACKET_INDEX;
      router_read_buff[ctr].readbuff[EAST_BUFF]= INVALID_PACKET_INDEX;
      router_read_buff[ctr].readbuff[WEST_BUFF]= INVALID_PACKET_INDEX;

      router_write_buff[ctr].writebuff[NODE_BUFF]= INVALID_PACKET_INDEX;
      router_write_buff[ctr].writebuff[NORTH_BUFF]= INVALID_PACKET_INDEX;
      router_write_buff[ctr].writebuff[SOUTH_BUFF]= INVALID_PACKET_INDEX;
      router_write_buff[ctr].writebuff[EAST_BUFF]= INVALID_PACKET_INDEX;
      router_write_buff[ctr].writebuff[WEST_BUFF]= INVALID_PACKET_INDEX;

      router_switch_buff[ctr].nodebuffreq[NODE_BUFF]= false;
      router_switch_buff[ctr].nodebuffreq[NORTH_BUFF]= false;
      router_switch_buff[ctr].nodebuffreq[SOUTH_BUFF]= false;
      router_switch_buff[ctr].nodebuffreq[EAST_BUFF]= false;
      router_switch_buff[ctr].nodebuffreq[WEST_BUFF]= false;
      router_switch_buff[ctr].nodebuffack[NODE_BUFF]= false;
      router_switch_buff[ctr].nodebuffack[NORTH_BUFF]= false;
      router_switch_buff[ctr].nodebuffack[SOUTH_BUFF]= false;
      router_switch_buff[ctr].nodebuffack[EAST_BUFF]= false;
      router_switch_buff[ctr].nodebuffack[WEST_BUFF]= false;

      router_switch_buff[ctr].westbuffreq[NODE_BUFF]= false;
      router_switch_buff[ctr].westbuffreq[NORTH_BUFF]= false;
      router_switch_buff[ctr].westbuffreq[SOUTH_BUFF]= false;
      router_switch_buff[ctr].westbuffreq[EAST_BUFF]= false;
      router_switch_buff[ctr].westbuffreq[WEST_BUFF]= false;
      router_switch_buff[ctr].westbuffack[NODE_BUFF]= false;
      router_switch_buff[ctr].westbuffack[NORTH_BUFF]= false;
      router_switch_buff[ctr].westbuffack[SOUTH_BUFF]= false;
      router_switch_buff[ctr].westbuffack[EAST_BUFF]= false;
      router_switch_buff[ctr].westbuffack[WEST_BUFF]= false;

      router_switch_buff[ctr].eastbuffreq[NODE_BUFF]= false;
      router_switch_buff[ctr].eastbuffreq[NORTH_BUFF]= false;
      router_switch_buff[ctr].eastbuffreq[SOUTH_BUFF]= false;
      router_switch_buff[ctr].eastbuffreq[EAST_BUFF]= false;
      router_switch_buff[ctr].eastbuffreq[WEST_BUFF]= false;
      router_switch_buff[ctr].eastbuffack[NODE_BUFF]= false;
      router_switch_buff[ctr].eastbuffack[NORTH_BUFF]= false;
      router_switch_buff[ctr].eastbuffack[SOUTH_BUFF]= false;
      router_switch_buff[ctr].eastbuffack[EAST_BUFF]= false;
      router_switch_buff[ctr].eastbuffack[WEST_BUFF]= false;

      router_switch_buff[ctr].northbuffreq[NODE_BUFF]= false;
      router_switch_buff[ctr].northbuffreq[NORTH_BUFF]= false;
      router_switch_buff[ctr].northbuffreq[SOUTH_BUFF]= false;
      router_switch_buff[ctr].northbuffreq[EAST_BUFF]= false;
      router_switch_buff[ctr].northbuffreq[WEST_BUFF]= false;
      router_switch_buff[ctr].northbuffack[NODE_BUFF]= false;
      router_switch_buff[ctr].northbuffack[NORTH_BUFF]= false;
      router_switch_buff[ctr].northbuffack[SOUTH_BUFF]= false;
      router_switch_buff[ctr].northbuffack[EAST_BUFF]= false;
      router_switch_buff[ctr].northbuffack[WEST_BUFF]= false;

      router_switch_buff[ctr].southbuffreq[NODE_BUFF]= false;
      router_switch_buff[ctr].southbuffreq[NORTH_BUFF]= false;
      router_switch_buff[ctr].southbuffreq[SOUTH_BUFF]= false;
      router_switch_buff[ctr].southbuffreq[EAST_BUFF]= false;
      router_switch_buff[ctr].southbuffreq[WEST_BUFF]= false;
      router_switch_buff[ctr].southbuffack[NODE_BUFF]= false;
      router_switch_buff[ctr].southbuffack[NORTH_BUFF]= false;
      router_switch_buff[ctr].southbuffack[SOUTH_BUFF]= false;
      router_switch_buff[ctr].southbuffack[EAST_BUFF]= false;
      router_switch_buff[ctr].southbuffack[WEST_BUFF]= false;

      router_arbiter_buff[ctr].arbitertoken[NODE_BUFF] = EAST_PRIORITY;
      router_arbiter_buff[ctr].arbitertoken[NORTH_BUFF] = EAST_PRIORITY;
      router_arbiter_buff[ctr].arbitertoken[SOUTH_BUFF] = EAST_PRIORITY;
      router_arbiter_buff[ctr].arbitertoken[EAST_BUFF] = EAST_PRIORITY;
      router_arbiter_buff[ctr].arbitertoken[WEST_BUFF] = EAST_PRIORITY;

      cpacket_sent_status[ctr]= false;
      cpacket_received_status[ctr]= false;
      node_base_index[ctr] = start_packet_index[ctr];

      node_dest_id_x [ctr] = INVALID_ROUTER_INDEX;
      node_dest_id_y [ctr] = INVALID_ROUTER_INDEX;
      east_dest_id_x [ctr] = INVALID_ROUTER_INDEX;
      east_dest_id_y [ctr] = INVALID_ROUTER_INDEX;
      west_dest_id_x [ctr] = INVALID_ROUTER_INDEX;
      west_dest_id_y [ctr] = INVALID_ROUTER_INDEX;
      north_dest_id_x [ctr] = INVALID_ROUTER_INDEX;
      north_dest_id_y [ctr] = INVALID_ROUTER_INDEX;
      south_dest_id_x [ctr] = INVALID_ROUTER_INDEX;
      south_dest_id_y [ctr] = INVALID_ROUTER_INDEX;

      node_packet_index [ctr] = INVALID_PACKET_INDEX;
      east_packet_index [ctr] = INVALID_PACKET_INDEX;
      west_packet_index [ctr] = INVALID_PACKET_INDEX;
      north_packet_index [ctr] = INVALID_PACKET_INDEX;
      south_packet_index [ctr] = INVALID_PACKET_INDEX;


      ctr ++;
   :: else ->
       run topology();
      break;
   od;

  }

}


proctype topology( )
{
  do
   :: 1 ->  /* process runs forever */
  d_step{
   /* Specification of mesh topology */
   /* The values must be copied after switching */
   /* Router 0 */
      if 
        :: router_write_buff[1].writebuff[WEST_BUFF] != INVALID_PACKET_INDEX  ->
                router_read_buff[0].readbuff[EAST_BUFF]= router_write_buff[1].writebuff[WEST_BUFF]; 
                router_write_buff[1].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX;

      :: router_write_buff[3].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX ->
           router_read_buff[0].readbuff[NORTH_BUFF]= router_write_buff[3].writebuff[SOUTH_BUFF];
           router_write_buff[3].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
  

   /* Router 1 */

       :: router_write_buff[0].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
              router_read_buff[1].readbuff[WEST_BUFF]= router_write_buff[0].writebuff[EAST_BUFF];
             router_write_buff[0].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;
  
      :: router_write_buff[2].writebuff[WEST_BUFF]  != INVALID_PACKET_INDEX -> 
         router_read_buff[1].readbuff[EAST_BUFF]= router_write_buff[2].writebuff[WEST_BUFF];
         router_write_buff[2].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX;
  
     :: router_write_buff[4].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX -> 
          router_read_buff[1].readbuff[NORTH_BUFF]= router_write_buff[4].writebuff[SOUTH_BUFF];
         router_write_buff[4].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
  
   /* Router 2 */
        :: router_write_buff[1].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
           router_read_buff[2].readbuff[WEST_BUFF]= router_write_buff[1].writebuff[EAST_BUFF];
            router_write_buff[1].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;
  
   :: router_write_buff[5].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX ->
           router_read_buff[2].readbuff[NORTH_BUFF]= router_write_buff[5].writebuff[SOUTH_BUFF];
           router_write_buff[5].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 3 */
       :: router_write_buff[4].writebuff[WEST_BUFF] != INVALID_PACKET_INDEX ->
          router_read_buff[3].readbuff[EAST_BUFF]= router_write_buff[4].writebuff[WEST_BUFF];
          router_write_buff[4].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX;

     ::router_write_buff[6].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX -> 
          router_read_buff[3].readbuff[NORTH_BUFF]= router_write_buff[6].writebuff[SOUTH_BUFF];
          router_write_buff[6].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;

      ::router_write_buff[0].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX -> 
          router_read_buff[3].readbuff[SOUTH_BUFF]= router_write_buff[0].writebuff[NORTH_BUFF];
         router_write_buff[0].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 4 */
        :: router_write_buff[3].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
            router_read_buff[4].readbuff[WEST_BUFF]= router_write_buff[3].writebuff[EAST_BUFF];
            router_write_buff[3].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;

         ::router_write_buff[5].writebuff[WEST_BUFF] != INVALID_PACKET_INDEX -> 
             router_read_buff[4].readbuff[EAST_BUFF]= router_write_buff[5].writebuff[WEST_BUFF];
             router_write_buff[5].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX;

         ::router_write_buff[7].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX ->
              router_read_buff[4].readbuff[NORTH_BUFF]= router_write_buff[7].writebuff[SOUTH_BUFF];
              router_write_buff[7].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;

         :: router_write_buff[1].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX ->
                router_read_buff[4].readbuff[SOUTH_BUFF]= router_write_buff[1].writebuff[NORTH_BUFF];
             router_write_buff[1].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 5 */
         ::router_write_buff[4].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
             router_read_buff[5].readbuff[WEST_BUFF]= router_write_buff[4].writebuff[EAST_BUFF];
              router_write_buff[4].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;

        :: router_write_buff[8].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX -> 
             router_read_buff[5].readbuff[NORTH_BUFF]= router_write_buff[8].writebuff[SOUTH_BUFF];
             router_write_buff[8].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;

       :: router_write_buff[2].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX ->      
            router_read_buff[5].readbuff[SOUTH_BUFF]= router_write_buff[2].writebuff[NORTH_BUFF];
           router_write_buff[2].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 6 */
       :: router_write_buff[7].writebuff[WEST_BUFF] != INVALID_PACKET_INDEX -> 
             router_read_buff[6].readbuff[EAST_BUFF]= router_write_buff[7].writebuff[WEST_BUFF];
             router_write_buff[7].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX ;

       :: router_write_buff[3].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX ->  
             router_read_buff[6].readbuff[SOUTH_BUFF]= router_write_buff[3].writebuff[NORTH_BUFF];
             router_write_buff[3].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
 
   /* Router 7 */
        :: router_write_buff[6].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
              router_read_buff[7].readbuff[WEST_BUFF]= router_write_buff[6].writebuff[EAST_BUFF];
              router_write_buff[6].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;

         :: router_write_buff[8].writebuff[WEST_BUFF] != INVALID_PACKET_INDEX -> 
            router_read_buff[7].readbuff[EAST_BUFF]= router_write_buff[8].writebuff[WEST_BUFF];
           router_write_buff[8].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX;

      ::router_write_buff[4].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX -> 
         router_read_buff[7].readbuff[SOUTH_BUFF]= router_write_buff[4].writebuff[NORTH_BUFF];
          router_write_buff[4].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 8 */
        :: router_write_buff[7].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
             router_read_buff[8].readbuff[WEST_BUFF]= router_write_buff[7].writebuff[EAST_BUFF];
             router_write_buff[7].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;

       :: router_write_buff[5].writebuff[NORTH_BUFF]  != INVALID_PACKET_INDEX -> 
             router_read_buff[8].readbuff[SOUTH_BUFF]= router_write_buff[5].writebuff[NORTH_BUFF];
             router_write_buff[5].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
      :: skip
   fi;
   }
  od;
}

init {

  run startup();

}


   
