/***********************************************************************************************************************************************************
* Date : 22 July 2011 
*  Objective: Verify odd-even routing algorithm for 3X3 mesh
*  Properties to verity:
*                        - Every packet sent is received
*                        - Every packet follows a valid path
*                        - A path is valid only when all the nodes in the path belong to set
*                        - The path is adaptive
*  
************************************************************************************************************************************************************/

/* max number of nodes in system */
#define MAX_NODES   9  
#define MAX_ROUTERS   MAX_NODES 

#define MAX_PACKETS 9

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

/* router types */
#define ODD_TYPE  1
#define EVEN_TYPE 2

/* packet turn types */
#define EAST_SOUTH  1
#define EAST_NORTH  2
#define WEST_SOUTH  3
#define WEST_NORTH  4
#define SOUTH_EAST  5
#define SOUTH_WEST  6
#define NORTH_EAST  7
#define NORTH_WEST  8

/* routing dimensions */
#define MAX_DIM   4
#define EAST      0
#define WEST      1
#define NORTH     2
#define SOUTH     3
#define NOT_USED   1
#define AVAIL      2
#define USED       3


/* marking invalid packet index */
#define INVALID_PACKET_INDEX 99

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
hidden packet packet_list[MAX_NODES];

/* assuming that at any instance only one instance of any packet is alive */ 
bool cpacket_sent_status[MAX_PACKETS];
bool cpacket_received_status[MAX_PACKETS];

/* dual array, is received */
bool cpacket_received_status_at[MAX_NODES];
bool cpacket_received_status_from[MAX_NODES];

/* array for storing permitted routing dimensions*/
typedef dimensionlist { 
	byte nodeavailset[MAX_DIM];
	byte eastavailset[MAX_DIM];
	byte westavailset[MAX_DIM];
	byte northavailset[MAX_DIM];
	byte southavailset[MAX_DIM];
};

dimensionlist router_dim[MAX_ROUTERS];

/* array for storing read buffers for a router, the value indicates the packet index, into packet array */
typedef readbufflist { 
	byte readbuff[MAX_BUFF];
};

readbufflist router_read_buff[MAX_ROUTERS];

typedef writebufflist { 
	byte writebuff[MAX_BUFF];
};

writebufflist router_write_buff[MAX_ROUTERS];


/* Examples:
 router_read_buff[2][NORTH_BUFF] = 5 tells that there is an input available  from north side to router # 2, 
                                            and it corresponds to the packet, packet_list[5] in transmission,
                                            that is packet is of node 5 is available for transmission*/

/* router_read_buff[3][SOUTH_BUFF] = INVALID_PACKET_INDEX tells that the input buffer of the  south side to router # 3 is empty*/

hidden byte router_id_x[MAX_ROUTERS]; 
hidden byte router_id_y[MAX_ROUTERS]; 
hidden byte router_type[MAX_ROUTERS]; 

hidden  byte ctr;

byte packet_index [MAX_ROUTERS];

byte node_packet_index [MAX_ROUTERS];
byte node_dest_id_x [MAX_ROUTERS];
byte node_dest_id_y [MAX_ROUTERS];
byte node_src_id_x [MAX_ROUTERS];
byte node_src_id_y [MAX_ROUTERS];
int node_est_id_x [MAX_ROUTERS];
int node_est_id_y [MAX_ROUTERS];

byte west_packet_index [MAX_ROUTERS];
byte west_dest_id_x [MAX_ROUTERS];
byte west_dest_id_y [MAX_ROUTERS];
byte west_src_id_x [MAX_ROUTERS];
byte west_src_id_y [MAX_ROUTERS];
int west_est_id_x [MAX_ROUTERS];
int west_est_id_y [MAX_ROUTERS];

byte east_packet_index [MAX_ROUTERS];
byte east_dest_id_x [MAX_ROUTERS];
byte east_dest_id_y [MAX_ROUTERS];
byte east_src_id_x [MAX_ROUTERS];
byte east_src_id_y [MAX_ROUTERS];
int east_est_id_x [MAX_ROUTERS];
int east_est_id_y [MAX_ROUTERS];

byte north_packet_index [MAX_ROUTERS];
byte north_dest_id_x [MAX_ROUTERS];
byte north_dest_id_y [MAX_ROUTERS];
byte north_src_id_x [MAX_ROUTERS];
byte north_src_id_y [MAX_ROUTERS];
int north_est_id_x [MAX_ROUTERS];
int north_est_id_y [MAX_ROUTERS];

byte south_packet_index [MAX_ROUTERS];
byte south_dest_id_x [MAX_ROUTERS];
byte south_dest_id_y [MAX_ROUTERS];
byte south_src_id_x [MAX_ROUTERS];
byte south_src_id_y [MAX_ROUTERS];
int south_est_id_x [MAX_ROUTERS];
int south_est_id_y [MAX_ROUTERS];

/* packet tracking variable */
/* track packet */

hidden byte start_packet_index[MAX_PACKETS];
hidden byte end_packet_index[MAX_PACKETS];
hidden byte node_index ;
hidden byte node_base_index[MAX_NODES];

byte pktctr = 0; /* declared at top */
byte portctr = 0; /* declared at top */
byte rcvctr = 0;

byte testvar = 0;

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

            d_step{   /* change to atomic if any of the cond can block */
                if
                 :: node_base_index[id]!= INVALID_PACKET_INDEX && cpacket_sent_status[node_base_index[id]] == false -> 
                      router_read_buff[id].readbuff[NODE_BUFF] =node_base_index[id]; 
                      cpacket_sent_status[node_base_index[id]] = true; 
            
                 /* generate packet 1 */
                 :: node_base_index[id]!= INVALID_PACKET_INDEX && cpacket_received_status[node_base_index[id]] == true-> 
                   /**** Unmask this to keep sending packets in a loop *********/                    
                   if 
                     :: node_base_index[id] < end_packet_index[id] ->  
                        node_base_index[id] = node_base_index[id] + 1; 
                     :: node_base_index[id] == end_packet_index[id] ->  
                        node_base_index[id] = start_packet_index[id] ;
                     :: node_base_index[id] == INVALID_PACKET_INDEX -> 
                        node_base_index[id] = INVALID_PACKET_INDEX;
                  fi;
                   
                :: router_write_buff[id].writebuff[NODE_BUFF] != INVALID_PACKET_INDEX ->
                   packet_index[id] =  router_write_buff[id].writebuff[NODE_BUFF];
                   /* Set packet received to true */
                   cpacket_received_status_at[id] = true; 
                   cpacket_received_status_from[packet_list[packet_index[id]].pkt_index] = true; 
                   cpacket_received_status[packet_index[id]] = true;
                   router_write_buff[id].writebuff[NODE_BUFF] = INVALID_PACKET_INDEX;

                ::skip
                fi;
             }

       :: 1 -> 
           /* this is router part */
           /* logic for reading data and  arbitration */
           /* arbitration is not required as packet index is only circulated in node, which is one byte and it is switched
              synchronously */
           d_step {
              /* Note that following will be executed in sequence because of d_step, change if reqd */
             if
             :: router_read_buff[id].readbuff[NODE_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 node_packet_index [id] =  router_read_buff[id].readbuff[NODE_BUFF];

                 /* Get dest id */
                 node_dest_id_x [id] = packet_list[node_packet_index[id]].dest_index_x;
                 node_dest_id_y [id] = packet_list[node_packet_index[id]].dest_index_y;

                 /* Get src id */
                 node_src_id_x [id] = packet_list[node_packet_index[id]].src_index_x;
                 node_src_id_y [id] = packet_list[node_packet_index[id]].src_index_y;

                 /* Get est id */
                 node_est_id_x [id] = node_dest_id_x [id] - router_id_x[id];
                 node_est_id_y [id] = node_dest_id_y [id] - router_id_y[id];

                 /* Reinit port availability */
                 router_dim[id].nodeavailset[EAST] = NOT_USED; 
                 router_dim[id].nodeavailset[WEST] = NOT_USED; 
                 router_dim[id].nodeavailset[NORTH] = NOT_USED; 
                 router_dim[id].nodeavailset[SOUTH] = NOT_USED; 

                 if
                   :: node_est_id_x [id] == 0 && node_est_id_y [id] == 0 && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                        router_write_buff[id].writebuff[NODE_BUFF]  = node_packet_index[id]; 
                        router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX;
 
                   :: node_est_id_x [id] == 0 && node_est_id_y [id] < 0 ->
                     /******SEE IF THE ROUTING PATH MUST BE CHECKED IF IT NOT USED BEFORE SETTING IT TO AVAILABLE ******/
                        router_dim[id].nodeavailset[SOUTH] = AVAIL;

                   :: node_est_id_x [id] == 0 && node_est_id_y [id] > 0 ->
                        router_dim[id].nodeavailset[NORTH] = AVAIL;
                   
                   :: node_est_id_x [id] > 0 && node_est_id_y [id] == 0 ->
                        router_dim[id].nodeavailset[EAST] = AVAIL;

                   :: node_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == node_src_id_x [id]) && node_est_id_y [id] < 0 ->
                        router_dim[id].nodeavailset[SOUTH] = AVAIL;

                   :: node_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == node_src_id_x [id]) && node_est_id_y [id] > 0 ->
                        router_dim[id].nodeavailset[NORTH] = AVAIL;

                   :: node_est_id_x [id] > 0 && (node_dest_id_x [id] % 2 != 0 || node_est_id_x [id] != 1) ->
                        router_dim[id].nodeavailset[EAST] = AVAIL;
                          
                   :: node_est_id_x [id] < 0  ->
                        router_dim[id].nodeavailset[WEST] = AVAIL;

                   :: node_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == node_src_id_x [id]) && node_est_id_y [id] < 0 ->
                        router_dim[id].nodeavailset[SOUTH] = AVAIL;

                   :: node_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == node_src_id_x [id]) && node_est_id_y [id] > 0 ->
                        router_dim[id].nodeavailset[NORTH] = AVAIL;
                   :: skip
                 fi;

                 /*********check the available routes and take one of the permitted routes ******/  

                 if
              
                   :: router_dim[id].nodeavailset[EAST] == AVAIL ->
                      router_write_buff[id].writebuff[EAST_BUFF]  = node_packet_index[id]; 
                      router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].nodeavailset[EAST] = USED;
    
                   :: router_dim[id].nodeavailset[WEST] == AVAIL ->
                      router_write_buff[id].writebuff[WEST_BUFF]  = node_packet_index[id]; 
                      router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].nodeavailset[WEST] = USED;
   
                   :: router_dim[id].nodeavailset[NORTH] == AVAIL ->
                      router_write_buff[id].writebuff[NORTH_BUFF]  = node_packet_index[id]; 
                      router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].nodeavailset[NORTH] = USED;

                   :: router_dim[id].nodeavailset[SOUTH] == AVAIL ->
                      router_write_buff[id].writebuff[SOUTH_BUFF]  = node_packet_index[id]; 
                      router_read_buff[id].readbuff[NODE_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].nodeavailset[SOUTH] = USED;

                   ::skip
                  fi;




             :: router_read_buff[id].readbuff[EAST_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 east_packet_index [id] =  router_read_buff[id].readbuff[EAST_BUFF];

                 /* Get dest id */
                 east_dest_id_x [id] = packet_list[east_packet_index[id]].dest_index_x;
                 east_dest_id_y [id] = packet_list[east_packet_index[id]].dest_index_y;

                 /* Get src id */
                 east_src_id_x [id] = packet_list[east_packet_index[id]].src_index_x;
                 east_src_id_y [id] = packet_list[east_packet_index[id]].src_index_y;

                 /* Get est id */
                 east_est_id_x [id] = east_dest_id_x [id] - router_id_x[id];
                 east_est_id_y [id] = east_dest_id_y [id] - router_id_y[id];

                 /* Reinit port availability */
                 router_dim[id].eastavailset[EAST] = NOT_USED;
                 router_dim[id].eastavailset[WEST] = NOT_USED;
                 router_dim[id].eastavailset[NORTH] = NOT_USED;
                 router_dim[id].eastavailset[SOUTH] = NOT_USED;

                 if
                   :: east_est_id_x [id] == 0 && east_est_id_y [id] == 0 && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                        router_write_buff[id].writebuff[NODE_BUFF]  = east_packet_index[id]; 
                        router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX;
 
                   :: east_est_id_x [id] == 0 && east_est_id_y [id] < 0 ->
                     /******SEE IF THE ROUTING PATH MUST BE CHECKED IF IT NOT USED BEFORE SETTING IT TO AVAILABLE ******/
                        router_dim[id].eastavailset[SOUTH] = AVAIL;

                   :: east_est_id_x [id] == 0 && east_est_id_y [id] > 0 ->
                        router_dim[id].eastavailset[NORTH] = AVAIL;
                   
                   :: east_est_id_x [id] > 0 && east_est_id_y [id] == 0 ->
                        router_dim[id].eastavailset[EAST] = AVAIL;

                   :: east_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == east_src_id_x [id]) && east_est_id_y [id] < 0 ->
                        router_dim[id].eastavailset[SOUTH] = AVAIL;

                   :: east_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == east_src_id_x [id]) && east_est_id_y [id] > 0 ->
                        router_dim[id].eastavailset[NORTH] = AVAIL;

                   :: east_est_id_x [id] > 0 && (east_dest_id_x [id] % 2 != 0 || east_est_id_x [id] != 1) ->
                        router_dim[id].eastavailset[EAST] = AVAIL;
                          
                   :: east_est_id_x [id] < 0  ->
                        router_dim[id].eastavailset[WEST] = AVAIL;

                   :: east_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == east_src_id_x [id]) && east_est_id_y [id] < 0 ->
                        router_dim[id].eastavailset[SOUTH] = AVAIL;

                   :: east_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == east_src_id_x [id]) && east_est_id_y [id] > 0 ->
                        router_dim[id].eastavailset[NORTH] = AVAIL;
                   :: skip
                 fi;

                 /*********check the available routes and take one of the permitted routes ******/  

                 if
              
                   :: router_dim[id].eastavailset[EAST] == AVAIL ->
                      router_write_buff[id].writebuff[EAST_BUFF]  = east_packet_index[id]; 
                      router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].eastavailset[EAST] = USED;

                   :: router_dim[id].eastavailset[WEST] == AVAIL ->
                      router_write_buff[id].writebuff[WEST_BUFF]  = east_packet_index[id]; 
                      router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].eastavailset[WEST] = USED;

                   :: router_dim[id].eastavailset[NORTH] == AVAIL ->
                      router_write_buff[id].writebuff[NORTH_BUFF]  = east_packet_index[id]; 
                      router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].eastavailset[NORTH] = USED;

                   :: router_dim[id].eastavailset[SOUTH] == AVAIL ->
                      router_write_buff[id].writebuff[SOUTH_BUFF]  = east_packet_index[id]; 
                      router_read_buff[id].readbuff[EAST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].eastavailset[SOUTH] = USED;

                   ::skip
                  fi;



             :: router_read_buff[id].readbuff[WEST_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 west_packet_index [id] =  router_read_buff[id].readbuff[WEST_BUFF];

                 /* Get dest id */
                 west_dest_id_x [id] = packet_list[west_packet_index[id]].dest_index_x;
                 west_dest_id_y [id] = packet_list[west_packet_index[id]].dest_index_y;

                 /* Get src id */
                 west_src_id_x [id] = packet_list[west_packet_index[id]].src_index_x;
                 west_src_id_y [id] = packet_list[west_packet_index[id]].src_index_y;

                 /* Get est id */
                 west_est_id_x [id] = west_dest_id_x [id] - router_id_x[id];
                 west_est_id_y [id] = west_dest_id_y [id] - router_id_y[id];

                 /* Reinit port availability */
                 router_dim[id].westavailset[EAST] = NOT_USED;
                 router_dim[id].westavailset[WEST] = NOT_USED;
                 router_dim[id].westavailset[NORTH] = NOT_USED;
                 router_dim[id].westavailset[SOUTH] = NOT_USED;

                 if
                   :: west_est_id_x [id] == 0 && west_est_id_y [id] == 0 && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                        router_write_buff[id].writebuff[NODE_BUFF]  = west_packet_index[id]; 
                        router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX;
 
                   :: west_est_id_x [id] == 0 && west_est_id_y [id] < 0 ->
                     /******SEE IF THE ROUTING PATH MUST BE CHECKED IF IT NOT USED BEFORE SETTING IT TO AVAILABLE ******/
                        router_dim[id].westavailset[SOUTH] = AVAIL;

                   :: west_est_id_x [id] == 0 && west_est_id_y [id] > 0 ->
                        router_dim[id].westavailset[NORTH] = AVAIL;
                   
                   :: west_est_id_x [id] > 0 && west_est_id_y [id] == 0 ->
                        router_dim[id].westavailset[EAST] = AVAIL;

                   :: west_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == west_src_id_x [id]) && west_est_id_y [id] < 0 ->
                        router_dim[id].westavailset[SOUTH] = AVAIL;

                   :: west_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == west_src_id_x [id]) && west_est_id_y [id] > 0 ->
                        router_dim[id].westavailset[NORTH] = AVAIL;

                   :: west_est_id_x [id] > 0 && (west_dest_id_x [id] % 2 != 0 || west_est_id_x [id] != 1) ->
                        router_dim[id].westavailset[EAST] = AVAIL;
                          
                   :: west_est_id_x [id] < 0  ->
                        router_dim[id].westavailset[WEST] = AVAIL;

                   :: west_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == west_src_id_x [id]) && west_est_id_y [id] < 0 ->
                        router_dim[id].westavailset[SOUTH] = AVAIL;

                   :: west_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == west_src_id_x [id]) && west_est_id_y [id] > 0 ->
                        router_dim[id].westavailset[NORTH] = AVAIL;
                   :: skip
                 fi;

                 /*********check the available routes and take one of the permitted routes ******/  

                 if
              
                   :: router_dim[id].westavailset[EAST] == AVAIL ->
                      router_write_buff[id].writebuff[EAST_BUFF]  = west_packet_index[id]; 
                      router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].westavailset[EAST] = USED;

                   :: router_dim[id].westavailset[WEST] == AVAIL ->
                      router_write_buff[id].writebuff[WEST_BUFF]  = west_packet_index[id]; 
                      router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].westavailset[WEST] = USED;

                   :: router_dim[id].westavailset[NORTH] == AVAIL ->
                      router_write_buff[id].writebuff[NORTH_BUFF]  = west_packet_index[id]; 
                      router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].westavailset[NORTH] = USED;

                   :: router_dim[id].westavailset[SOUTH] == AVAIL ->
                      router_write_buff[id].writebuff[SOUTH_BUFF]  = west_packet_index[id]; 
                      router_read_buff[id].readbuff[WEST_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].westavailset[SOUTH] = USED;

                   ::skip
                  fi;





            :: router_read_buff[id].readbuff[NORTH_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 north_packet_index [id] =  router_read_buff[id].readbuff[NORTH_BUFF];

                 /* Get dest id */
                 north_dest_id_x [id] = packet_list[north_packet_index[id]].dest_index_x;
                 north_dest_id_y [id] = packet_list[north_packet_index[id]].dest_index_y;

                 /* Get src id */
                 north_src_id_x [id] = packet_list[north_packet_index[id]].src_index_x;
                 north_src_id_y [id] = packet_list[north_packet_index[id]].src_index_y;

                 /* Get est id */
                 north_est_id_x [id] = north_dest_id_x [id] - router_id_x[id];
                 north_est_id_y [id] = north_dest_id_y [id] - router_id_y[id];

                 /* Reinit port availability */
                 router_dim[id].northavailset[EAST] = NOT_USED;
                 router_dim[id].northavailset[WEST] = NOT_USED;
                 router_dim[id].northavailset[NORTH] = NOT_USED;
                 router_dim[id].northavailset[SOUTH] = NOT_USED;

                 if
                   :: north_est_id_x [id] == 0 && north_est_id_y [id] == 0 && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                        router_write_buff[id].writebuff[NODE_BUFF]  = north_packet_index[id]; 
                        router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
 
                   :: north_est_id_x [id] == 0 && north_est_id_y [id] < 0 ->
                     /******SEE IF THE ROUTING PATH MUST BE CHECKED IF IT NOT USED BEFORE SETTING IT TO AVAILABLE ******/
                        router_dim[id].northavailset[SOUTH] = AVAIL;

                   :: north_est_id_x [id] == 0 && north_est_id_y [id] > 0 ->
                        router_dim[id].northavailset[NORTH] = AVAIL;
                   
                   :: north_est_id_x [id] > 0 && north_est_id_y [id] == 0 ->
                        router_dim[id].northavailset[EAST] = AVAIL;

                   :: north_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == north_src_id_x [id]) && north_est_id_y [id] < 0 ->
                        router_dim[id].northavailset[SOUTH] = AVAIL;

                   :: north_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == north_src_id_x [id]) && north_est_id_y [id] > 0 ->
                        router_dim[id].northavailset[NORTH] = AVAIL;

                   :: north_est_id_x [id] > 0 && (north_dest_id_x [id] % 2 != 0 || north_est_id_x [id] != 1) ->
                        router_dim[id].northavailset[EAST] = AVAIL;
                          
                   :: north_est_id_x [id] < 0  ->
                        router_dim[id].northavailset[WEST] = AVAIL;

                   :: north_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == north_src_id_x [id]) && north_est_id_y [id] < 0 ->
                        router_dim[id].northavailset[SOUTH] = AVAIL;

                   :: north_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == north_src_id_x [id]) && north_est_id_y [id] > 0 ->
                        router_dim[id].northavailset[NORTH] = AVAIL;
                   :: skip
                 fi;

                 /*********check the available routes and take one of the permitted routes ******/  

                 if
              
                   :: router_dim[id].northavailset[EAST] == AVAIL ->
                      router_write_buff[id].writebuff[EAST_BUFF]  = north_packet_index[id]; 
                      router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].northavailset[EAST] = USED;

                   :: router_dim[id].northavailset[WEST] == AVAIL ->
                      router_write_buff[id].writebuff[WEST_BUFF]  = north_packet_index[id]; 
                      router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].northavailset[WEST] = USED;
   
                   :: router_dim[id].northavailset[NORTH] == AVAIL ->
                      router_write_buff[id].writebuff[NORTH_BUFF]  = north_packet_index[id]; 
                      router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].northavailset[NORTH] = USED;

                   :: router_dim[id].northavailset[SOUTH] == AVAIL ->
                      router_write_buff[id].writebuff[SOUTH_BUFF]  = north_packet_index[id]; 
                      router_read_buff[id].readbuff[NORTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].northavailset[SOUTH] = USED;

                  ::skip
                  fi;




            :: router_read_buff[id].readbuff[SOUTH_BUFF] != INVALID_PACKET_INDEX ->

                 /* valid packet present here generated by node */
                 south_packet_index [id] =  router_read_buff[id].readbuff[SOUTH_BUFF];


                 /* Get dest id */
                 south_dest_id_x [id] = packet_list[south_packet_index[id]].dest_index_x;
                 south_dest_id_y [id] = packet_list[south_packet_index[id]].dest_index_y;

                 /* Get src id */
                 south_src_id_x [id] = packet_list[south_packet_index[id]].src_index_x;
                 south_src_id_y [id] = packet_list[south_packet_index[id]].src_index_y;

                 /* Get est id */
                 south_est_id_x [id] = south_dest_id_x [id] - router_id_x[id];
                 south_est_id_y [id] = south_dest_id_y [id] - router_id_y[id];

                 /* Reinit port availability */
                 router_dim[id].southavailset[EAST] = NOT_USED;
                 router_dim[id].southavailset[WEST] = NOT_USED;
                 router_dim[id].southavailset[NORTH] = NOT_USED;
                 router_dim[id].southavailset[SOUTH] = NOT_USED;

                 if
                   :: south_est_id_x [id] == 0 && south_est_id_y [id] == 0 && router_write_buff[id].writebuff[NODE_BUFF]  == INVALID_PACKET_INDEX ->
                        router_write_buff[id].writebuff[NODE_BUFF]  = south_packet_index[id]; 
                        router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
 
                   :: south_est_id_x [id] == 0 && south_est_id_y [id] < 0 ->
                     /******SEE IF THE ROUTING PATH MUST BE CHECKED IF IT NOT USED BEFORE SETTING IT TO AVAILABLE ******/
                        router_dim[id].southavailset[SOUTH] = AVAIL;

                   :: south_est_id_x [id] == 0 && south_est_id_y [id] > 0 ->
                        router_dim[id].southavailset[NORTH] = AVAIL;
                   
                   :: south_est_id_x [id] > 0 && south_est_id_y [id] == 0 ->
                        router_dim[id].southavailset[EAST] = AVAIL;

                   :: south_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == south_src_id_x [id]) && south_est_id_y [id] < 0 ->
                        router_dim[id].southavailset[SOUTH] = AVAIL;

                   :: south_est_id_x [id] > 0 && (router_type [id] == ODD_TYPE || router_id_x[id] == south_src_id_x [id]) && south_est_id_y [id] > 0 ->
                        router_dim[id].southavailset[NORTH] = AVAIL;

                   :: south_est_id_x [id] > 0 && (south_dest_id_x [id] % 2 != 0 || south_est_id_x [id] != 1) ->
                        router_dim[id].southavailset[EAST] = AVAIL;
                          
                   :: south_est_id_x [id] < 0  ->
                        router_dim[id].southavailset[WEST] = AVAIL;

                   :: south_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == south_src_id_x [id]) && south_est_id_y [id] < 0 ->
                        router_dim[id].southavailset[SOUTH] = AVAIL;

                   :: south_est_id_x [id] < 0 && (router_type [id] == EVEN_TYPE || router_id_x[id] == south_src_id_x [id]) && south_est_id_y [id] > 0 ->
                        router_dim[id].southavailset[NORTH] = AVAIL;
                   :: skip
                 fi;

                 /*********check the available routes and take one of the permitted routes ******/  

                 if
              
                   :: router_dim[id].southavailset[EAST] == AVAIL ->
                      router_write_buff[id].writebuff[EAST_BUFF]  = south_packet_index[id]; 
                      router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].southavailset[EAST] = USED;

                   :: router_dim[id].southavailset[WEST] == AVAIL ->
                      router_write_buff[id].writebuff[WEST_BUFF]  = south_packet_index[id]; 
                      router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].southavailset[WEST] = USED;

                   :: router_dim[id].southavailset[NORTH] == AVAIL ->
                      router_write_buff[id].writebuff[NORTH_BUFF]  = south_packet_index[id]; 
                      router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].southavailset[NORTH] = USED;

                   :: router_dim[id].southavailset[SOUTH] == AVAIL ->
                      router_write_buff[id].writebuff[SOUTH_BUFF]  = south_packet_index[id]; 
                      router_read_buff[id].readbuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;
                      router_dim[id].southavailset[SOUTH] = USED;

                ::skip
                  fi;


             :: skip
            
             fi;
        } /* d_setp over */

       fi; /* rotuer action over */

   od;   /* top do loop */
}


/*This process initializes packets and starts up the router */
proctype startup () 
{

 /* Intialize packet_list array */ 

    /* Node 0 data */
    /* node 0 has 2 packets */
    /* start_packet_index[0]= INVALID_PACKET_INDEX; */
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
   packet_list[node_index+1].pkt_index = 0;
   packet_list[node_index+1].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+1].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+1].payload=44;   

   packet_list[node_index+2].dest_index_x = ROUTER_ID_2_x; 
   packet_list[node_index+2].dest_index_y = ROUTER_ID_2_y; 
   packet_list[node_index+2].pkt_index = 0;
   packet_list[node_index+2].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+2].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+2].payload=44;   

   packet_list[node_index+3].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index+3].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index+3].pkt_index = 0;
   packet_list[node_index+3].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+3].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+3].payload=44;   

   packet_list[node_index+4].dest_index_x = ROUTER_ID_4_x; 
   packet_list[node_index+4].dest_index_y = ROUTER_ID_4_y; 
   packet_list[node_index+4].pkt_index = 0;
   packet_list[node_index+4].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+4].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+4].payload=44;   

   packet_list[node_index+5].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index+5].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index+5].pkt_index = 0;
   packet_list[node_index+5].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+5].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+5].payload=44;   

   packet_list[node_index+6].dest_index_x = ROUTER_ID_6_x; 
   packet_list[node_index+6].dest_index_y = ROUTER_ID_6_y; 
   packet_list[node_index+6].pkt_index = 0;
   packet_list[node_index+6].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+6].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+6].payload=44;   

   packet_list[node_index+7].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index+7].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index+7].pkt_index = 0;
   packet_list[node_index+7].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+7].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+7].payload=44;   

   packet_list[node_index+8].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index+8].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index+8].pkt_index = 0;
   packet_list[node_index+8].src_index_x =ROUTER_ID_0_x;
   packet_list[node_index+8].src_index_y =ROUTER_ID_0_y;
   packet_list[node_index+8].payload=44;   

    /* Node 1 data */
    /* node 1 has 2 packets */
    start_packet_index[1]= INVALID_PACKET_INDEX; 
    /*  start_packet_index[1] = 1; */
    end_packet_index[1]   = 1;

   node_index = 1;

   packet_list[node_index].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index].pkt_index = 1;
   packet_list[node_index].src_index_x =ROUTER_ID_1_x;
   packet_list[node_index].src_index_y =ROUTER_ID_1_y;
   packet_list[node_index].payload=44;   


    /* Node 2 data */
    /* node 2 has 2 packets */
    start_packet_index[2]= INVALID_PACKET_INDEX;  
    /* start_packet_index[2] = 2; */
    end_packet_index[2]   = 2;

   node_index = 2;

   packet_list[node_index].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index].pkt_index = 2;
   packet_list[node_index].src_index_x =ROUTER_ID_2_x;
   packet_list[node_index].src_index_y =ROUTER_ID_2_y;
   packet_list[node_index].payload=44;   



    /* Node 3 data */
    /* node 3 has 2 packets */
    start_packet_index[3]= INVALID_PACKET_INDEX; 
    /* start_packet_index[3] = 3; */ 
    end_packet_index[3]   = 3;

   node_index = 3;

   packet_list[node_index].dest_index_x = ROUTER_ID_7_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_7_y; 
   packet_list[node_index].pkt_index = 3;
   packet_list[node_index].src_index_x =ROUTER_ID_3_x;
   packet_list[node_index].src_index_y =ROUTER_ID_3_y;
   packet_list[node_index].payload=44;   



    /* Node 4 data */
    /* node 4 has 2 packets */
    start_packet_index[4]= INVALID_PACKET_INDEX; 
    /* start_packet_index[4] = 4; */
    end_packet_index[4]   = 4;

   node_index = 4;

   packet_list[node_index].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index].pkt_index = 4;
   packet_list[node_index].src_index_x =ROUTER_ID_4_x;
   packet_list[node_index].src_index_y =ROUTER_ID_4_y;
   packet_list[node_index].payload=44;   



    /* Node 5 data */
    /* node 5 has 2 packets */
    start_packet_index[5]= INVALID_PACKET_INDEX; 
    /* start_packet_index[5] = 5; */
    end_packet_index[5]   = 5;

   node_index = 5;

   packet_list[node_index].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index].pkt_index = 5;
   packet_list[node_index].src_index_x =ROUTER_ID_5_x;
   packet_list[node_index].src_index_y =ROUTER_ID_5_y;
   packet_list[node_index].payload=44;   



    /* Node 6 data */
    /* node 6 has 2 packets */
    start_packet_index[6]= INVALID_PACKET_INDEX; 
    /* start_packet_index[6] = 6; */
    end_packet_index[6]   = 6;

   node_index = 6;

   packet_list[node_index].dest_index_x = ROUTER_ID_8_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_8_y; 
   packet_list[node_index].pkt_index = 6;
   packet_list[node_index].src_index_x =ROUTER_ID_6_x;
   packet_list[node_index].src_index_y =ROUTER_ID_6_y;
   packet_list[node_index].payload=44;   


 
    /* Node 7 data */
    /* node 7 has 2 packets */
    start_packet_index[7]= INVALID_PACKET_INDEX; 
    /* start_packet_index[7] = 7; */
    end_packet_index[7]   = 7;

   node_index = 7;

   packet_list[node_index].dest_index_x = ROUTER_ID_5_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_5_y; 
   packet_list[node_index].pkt_index = 7;
   packet_list[node_index].src_index_x =ROUTER_ID_7_x;
   packet_list[node_index].src_index_y =ROUTER_ID_7_y;
   packet_list[node_index].payload=44;   


   /* Node 8 data */
    /* node 8 has 2 packets */
    start_packet_index[8]= INVALID_PACKET_INDEX; 
    /* start_packet_index[8] = 8; */
    end_packet_index[8]   = 8;

   node_index = 8;

   packet_list[node_index].dest_index_x = ROUTER_ID_3_x; 
   packet_list[node_index].dest_index_y = ROUTER_ID_3_y; 
   packet_list[node_index].pkt_index = 8;
   packet_list[node_index].src_index_x =ROUTER_ID_8_x;
   packet_list[node_index].src_index_y =ROUTER_ID_8_y;
   packet_list[node_index].payload=44;   
   /* Intialize packet_list array, packets at each node */ 

 
   /*Initialise router id */
   router_id_x[0] = ROUTER_ID_0_x;  
   router_id_y[0] = ROUTER_ID_0_y;  
   router_type[0] = EVEN_TYPE;  

   router_id_x[1] = ROUTER_ID_1_x;  
   router_id_y[1] = ROUTER_ID_1_y;  
   router_type[1] = ODD_TYPE;  

   router_id_x[2] = ROUTER_ID_2_x;  
   router_id_y[2] = ROUTER_ID_2_y;  
   router_type[2] = EVEN_TYPE;  

   router_id_x[3] = ROUTER_ID_3_x;  
   router_id_y[3] = ROUTER_ID_3_y;  
   router_type[3] = EVEN_TYPE;  

   router_id_x[4] = ROUTER_ID_4_x;  
   router_id_y[4] = ROUTER_ID_4_y;  
   router_type[4] = ODD_TYPE;  

   router_id_x[5] = ROUTER_ID_5_x;  
   router_id_y[5] = ROUTER_ID_5_y;  
   router_type[5] = EVEN_TYPE;  

   router_id_x[6] = ROUTER_ID_6_x;  
   router_id_y[6] = ROUTER_ID_6_y;  
   router_type[6] = EVEN_TYPE;  

   router_id_x[7] = ROUTER_ID_7_x;  
   router_id_y[7] = ROUTER_ID_7_y;  
   router_type[7] = ODD_TYPE;  

   router_id_x[8] = ROUTER_ID_8_x;  
   router_id_y[8] = ROUTER_ID_8_y;  
   router_type[8] = EVEN_TYPE;  

 
   atomic{
    do 
     :: pktctr < MAX_PACKETS ->
         cpacket_sent_status[pktctr]= false;
         cpacket_received_status[pktctr]= false;
      pktctr ++;
     :: else ->
        break;
    od;

    }


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

      cpacket_received_status_at[ctr]= false;
      cpacket_received_status_from[ctr]= false;
      node_base_index[ctr] = start_packet_index[ctr];
      
      router_dim[ctr].nodeavailset[EAST] = NOT_USED;
      router_dim[ctr].nodeavailset[WEST] = NOT_USED;
      router_dim[ctr].nodeavailset[NORTH] = NOT_USED;
      router_dim[ctr].nodeavailset[SOUTH] = NOT_USED;

      router_dim[ctr].eastavailset[EAST] = NOT_USED;
      router_dim[ctr].eastavailset[WEST] = NOT_USED;
      router_dim[ctr].eastavailset[NORTH] = NOT_USED;
      router_dim[ctr].eastavailset[SOUTH] = NOT_USED;

      router_dim[ctr].westavailset[EAST] = NOT_USED;
      router_dim[ctr].westavailset[WEST] = NOT_USED;
      router_dim[ctr].westavailset[NORTH] = NOT_USED;
      router_dim[ctr].westavailset[SOUTH] = NOT_USED;

      router_dim[ctr].northavailset[EAST] = NOT_USED;
      router_dim[ctr].northavailset[WEST] = NOT_USED;
      router_dim[ctr].northavailset[NORTH] = NOT_USED;
      router_dim[ctr].northavailset[SOUTH] = NOT_USED;

      router_dim[ctr].southavailset[EAST] = NOT_USED;
      router_dim[ctr].southavailset[WEST] = NOT_USED;
      router_dim[ctr].southavailset[NORTH] = NOT_USED;
      router_dim[ctr].southavailset[SOUTH] = NOT_USED;

      node_packet_index [ctr] = INVALID_PACKET_INDEX;
      east_packet_index [ctr] = INVALID_PACKET_INDEX;
      west_packet_index [ctr] = INVALID_PACKET_INDEX;
      north_packet_index [ctr] = INVALID_PACKET_INDEX;
      south_packet_index [ctr] = INVALID_PACKET_INDEX;

      node_dest_id_x [ctr] = INVALID_ROUTER_INDEX ;
      node_dest_id_y [ctr] = INVALID_ROUTER_INDEX ;
      node_src_id_x [ctr] = INVALID_ROUTER_INDEX ;
      node_src_id_y [ctr] = INVALID_ROUTER_INDEX ;
      node_est_id_x [ctr] = INVALID_ROUTER_INDEX ;
      node_est_id_y [ctr] = INVALID_ROUTER_INDEX ;

      east_dest_id_x [ctr] = INVALID_ROUTER_INDEX ;
      east_dest_id_y [ctr] = INVALID_ROUTER_INDEX ;
      east_src_id_x [ctr] = INVALID_ROUTER_INDEX ;
      east_src_id_y [ctr] = INVALID_ROUTER_INDEX ;
      east_est_id_x [ctr] = INVALID_ROUTER_INDEX ;
      east_est_id_y [ctr] = INVALID_ROUTER_INDEX ;

      west_dest_id_x [ctr] = INVALID_ROUTER_INDEX ;
      west_dest_id_y [ctr] = INVALID_ROUTER_INDEX ;
      west_src_id_x [ctr] = INVALID_ROUTER_INDEX ;
      west_src_id_y [ctr] = INVALID_ROUTER_INDEX ;
      west_est_id_x [ctr] = INVALID_ROUTER_INDEX ;
      west_est_id_y [ctr] = INVALID_ROUTER_INDEX ;

      north_dest_id_x [ctr] = INVALID_ROUTER_INDEX ;
      north_dest_id_y [ctr] = INVALID_ROUTER_INDEX ;
      north_src_id_x [ctr] = INVALID_ROUTER_INDEX ;
      north_src_id_y [ctr] = INVALID_ROUTER_INDEX ;
      north_est_id_x [ctr] = INVALID_ROUTER_INDEX ;
      north_est_id_y [ctr] = INVALID_ROUTER_INDEX ;

      south_dest_id_x [ctr] = INVALID_ROUTER_INDEX ;
      south_dest_id_y [ctr] = INVALID_ROUTER_INDEX ;
      south_src_id_x [ctr] = INVALID_ROUTER_INDEX ;
      south_src_id_y [ctr] = INVALID_ROUTER_INDEX ;
      south_est_id_x [ctr] = INVALID_ROUTER_INDEX ;
      south_est_id_y [ctr] = INVALID_ROUTER_INDEX ;

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

     :: router_write_buff[6].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX -> 
         router_read_buff[3].readbuff[NORTH_BUFF]= router_write_buff[6].writebuff[SOUTH_BUFF];
         router_write_buff[6].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;

     :: router_write_buff[0].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX -> 
         router_read_buff[3].readbuff[SOUTH_BUFF]= router_write_buff[0].writebuff[NORTH_BUFF];
         router_write_buff[0].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 4 */
     :: router_write_buff[3].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
         router_read_buff[4].readbuff[WEST_BUFF]= router_write_buff[3].writebuff[EAST_BUFF];
         router_write_buff[3].writebuff[EAST_BUFF] = INVALID_PACKET_INDEX;

     ::router_write_buff[5].writebuff[WEST_BUFF] != INVALID_PACKET_INDEX -> 
        router_read_buff[4].readbuff[EAST_BUFF]= router_write_buff[5].writebuff[WEST_BUFF];
        router_write_buff[5].writebuff[WEST_BUFF] = INVALID_PACKET_INDEX;

     :: router_write_buff[7].writebuff[SOUTH_BUFF] != INVALID_PACKET_INDEX ->
         router_read_buff[4].readbuff[NORTH_BUFF]= router_write_buff[7].writebuff[SOUTH_BUFF];
         router_write_buff[7].writebuff[SOUTH_BUFF] = INVALID_PACKET_INDEX;

     :: router_write_buff[1].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX ->
         router_read_buff[4].readbuff[SOUTH_BUFF]= router_write_buff[1].writebuff[NORTH_BUFF];
         router_write_buff[1].writebuff[NORTH_BUFF] = INVALID_PACKET_INDEX;

   /* Router 5 */
     :: router_write_buff[4].writebuff[EAST_BUFF] != INVALID_PACKET_INDEX -> 
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

     :: router_write_buff[4].writebuff[NORTH_BUFF] != INVALID_PACKET_INDEX -> 
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


   
