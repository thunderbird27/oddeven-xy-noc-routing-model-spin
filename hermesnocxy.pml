/************************************************************************************************************************
* Date : 09 August 2011 
*  Objective: Model 3X3 synchronous NoC in mesh with XY routing algorithm and priority based round robin algorithm
*************************************************************************************************************************/

#define MAX_ROUTERS   9 
#define MAX_PACKETS   10 

/* marking invalid packet index */
#define INVALID_PACKET_INDEX 99
#define INVALID_ROUTER_INDEX 11
#define INVALID_BUFF 6

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

/* define switch status*/
#define FREE  0
#define USED  1

/* define input port, output port*/
#define FALSE_VAL  0
#define TRUE_VAL  1

hidden byte router_id_x[MAX_ROUTERS]; 
hidden byte router_id_y[MAX_ROUTERS]; 

typedef arbbuff_g { 
 bool req_g[MAX_BUFF];
 bool ack_g[MAX_BUFF];
}
arbbuff_g arb_buff_g[MAX_BUFF];

/* global state variables */
typedef port_status { 
  bool inp_status_g[5];  /*shared variable betn routers */
  byte readbuff_g[MAX_BUFF];
  byte writebuff_g[MAX_BUFF];
  arbbuff_g arb_buff_g[MAX_BUFF];
  byte arbitertoken_g [MAX_BUFF];
}
port_status router_id[MAX_ROUTERS];


typedef arbbuff { 
  bool req[MAX_BUFF];
  bool ack[MAX_BUFF];
}
hidden arbbuff arb_buff[MAX_BUFF];

/* stateless variables */
typedef current_status { 
  bool inp_status_h[5];
  bool output_status_h[5];
  byte readbuff_h[MAX_BUFF];
  byte writebuff_h[MAX_BUFF];
  byte start_packet_index;
  byte end_packet_index;
  byte packet_base_index;
  arbbuff arb_buff[MAX_BUFF];
  byte arbitertoken [MAX_BUFF];
  byte input_output_connection_map_h[MAX_BUFF];
  byte input_output_connection_port_h[MAX_BUFF];
}
hidden current_status router[MAX_ROUTERS];

/* you can sequentially number input and output ports of all routers and 
   keep this mapping. Since, this is a read-only info it is stored in a stateless
   variable */

typedef packet { 
 
/* valid for 128 source/dest nodes */
   byte dest_index_x;     
   byte dest_index_y;     
   byte pkt_index;
   byte src_index_x;
   byte src_index_y;
   byte hopcount;     /* range 0-127 */

 };

/* Once packets are initialized, their data remains constant, by making it hidden, you avoid
   it being part of state space. : Help in scaling verification.
*/
hidden packet packet_list[MAX_PACKETS];

typedef route_stats { 
  byte txctr;
  byte rcvctr;
  byte route[MAX_ROUTERS];
  bool packet_send;
  bool packet_receive;
}

hidden route_stats packet_status[MAX_PACKETS];

byte testvar = 0;

proctype router_node( int router_index )
{
 byte pectr = 0; /* declared at top */
 byte swctr = 0; /* declared at top */
 byte arbctr = 0; /* declared at top */
 byte topologyctr = 0; /* declared at top */
 byte updtctr = 0; /* declared at top */

  do
  :: 1 ->

    pectr = 0; 
    swctr = 0; 
    arbctr = 0; 
    topologyctr = 0; 
    updtctr = 0; 

    d_step{
           /* copy global state to current state */
          do 
            :: pectr < MAX_BUFF  ->                 
               router[router_index].inp_status_h[pectr] = router_id[router_index].inp_status_g[pectr];
               router[router_index].readbuff_h[pectr] = router_id[router_index].readbuff_g[pectr];
               router[router_index].writebuff_h[pectr] = router_id[router_index].writebuff_g[pectr];
               router[router_index].arb_buff[pectr].req[NODE_BUFF]  = router_id[router_index].arb_buff_g[pectr].req_g[NODE_BUFF];  
               router[router_index].arb_buff[pectr].req[EAST_BUFF]  = router_id[router_index].arb_buff_g[pectr].req_g[EAST_BUFF];  
               router[router_index].arb_buff[pectr].req[WEST_BUFF]  = router_id[router_index].arb_buff_g[pectr].req_g[WEST_BUFF];  
               router[router_index].arb_buff[pectr].req[NORTH_BUFF]  = router_id[router_index].arb_buff_g[pectr].req_g[NORTH_BUFF];  
               router[router_index].arb_buff[pectr].req[SOUTH_BUFF]  = router_id[router_index].arb_buff_g[pectr].req_g[SOUTH_BUFF];  
               router[router_index].arb_buff[pectr].ack[NODE_BUFF]  = router_id[router_index].arb_buff_g[pectr].ack_g[NODE_BUFF];  
               router[router_index].arb_buff[pectr].ack[EAST_BUFF]  = router_id[router_index].arb_buff_g[pectr].ack_g[EAST_BUFF];  
               router[router_index].arb_buff[pectr].ack[WEST_BUFF]  = router_id[router_index].arb_buff_g[pectr].ack_g[WEST_BUFF];  
               router[router_index].arb_buff[pectr].ack[NORTH_BUFF]  = router_id[router_index].arb_buff_g[pectr].ack_g[NORTH_BUFF];  
               router[router_index].arb_buff[pectr].ack[SOUTH_BUFF]  = router_id[router_index].arb_buff_g[pectr].ack_g[SOUTH_BUFF];  
               router[router_index].arbitertoken[pectr] = router_id[router_index].arbitertoken_g[pectr];
               pectr ++;
            :: else ->
                break;
           od;            
 
          if  
             /* inject packet into network */
             :: router[router_index].inp_status_h[NODE_BUFF]  == FREE && router[router_index].packet_base_index != INVALID_PACKET_INDEX  -> 
                /* Load the packet into buffer*/
                router[router_index].readbuff_h[NODE_BUFF] = router[router_index].packet_base_index;
                packet_list[router[router_index].readbuff_h[NODE_BUFF]].hopcount = 0;
                router[router_index].inp_status_h[NODE_BUFF]  = USED;  
                packet_status[router[router_index].readbuff_h[NODE_BUFF]].txctr =  packet_status[router[router_index].readbuff_h[NODE_BUFF]].txctr + 1; 
                packet_status[router[router_index].readbuff_h[NODE_BUFF]].packet_send = TRUE_VAL;  
                if
                  :: router[router_index].packet_base_index < router[router_index].end_packet_index ->
                     router[router_index].packet_base_index = router[router_index].packet_base_index + 1;
                  :: router[router_index].packet_base_index == router[router_index].end_packet_index ->
                     router[router_index].packet_base_index = router[router_index].start_packet_index;
                  :: skip
                fi; 

             :: skip        
          fi;

          /* Now execute sequentially (i) switch function 
            (ii) arbitration */
           
            /* these two functions read the updated stateless variables and 
               perform their computations */
          do 
            :: swctr < MAX_BUFF  ->
             /* handle i-th switch update */
             /* current state read */
             if
               :: router[router_index].inp_status_h[swctr] == USED && router[router_index].readbuff_h[swctr] != INVALID_PACKET_INDEX ->

                /* You may need additional data for the packet i.e.
                   source, destination, where to route it etc.
                   declare all of these in a structure, create an array
                   of hidden variables (its a read-only info)
                    out of them.. and use only index to this array as ref.
                    Note that currently inp_status_g is boolean, you may
                    need to additionally keep int cur_pack_id_g[][] along 
                    with it.
                */
              

                 if
                  /* switch east bound if X of destination address is greater than X of current router address*/
                 :: packet_list[router[router_index].readbuff_h[swctr]].dest_index_x > router_id_x[router_index] ->
                    if 
                     :: router[router_index].arb_buff[swctr].ack[EAST_BUFF] == FALSE_VAL -> 
                        router[router_index].arb_buff[swctr].req[EAST_BUFF] = TRUE_VAL;    
                     :: router[router_index].arb_buff[swctr].ack[EAST_BUFF] == TRUE_VAL && router[router_index].writebuff_h[EAST_BUFF] == INVALID_PACKET_INDEX -> 
                        router[router_index].writebuff_h[EAST_BUFF]  = router[router_index].readbuff_h[swctr]; 
                        router[router_index].output_status_h[EAST_BUFF] = USED;
                        packet_status[router[router_index].readbuff_h[swctr]].route[packet_list[router[router_index].readbuff_h[swctr]].hopcount] = router_index;    
                        packet_list[router[router_index].readbuff_h[swctr]].hopcount = packet_list[router[router_index].readbuff_h[swctr]].hopcount + 1;
                        router[router_index].readbuff_h[swctr] = INVALID_PACKET_INDEX; 
                        router[router_index].inp_status_h[swctr] = FREE;
                        router[router_index].arb_buff[swctr].req[EAST_BUFF]  = FALSE_VAL;
                     :: skip        
                   fi;

                  /* switch west bound if X of destination address is less than X of current router address*/
                 :: packet_list[router[router_index].readbuff_h[swctr]].dest_index_x < router_id_x[router_index] ->
                    if
                      :: router[router_index].arb_buff[swctr].ack[WEST_BUFF] == FALSE_VAL -> 
                         router[router_index].arb_buff[swctr].req[WEST_BUFF]  = TRUE_VAL;
                      :: router[router_index].arb_buff[swctr].ack[WEST_BUFF] == TRUE_VAL && router[router_index].writebuff_h[WEST_BUFF]  == INVALID_PACKET_INDEX -> 
                         router[router_index].writebuff_h[WEST_BUFF]  = router[router_index].readbuff_h[swctr]; 
                         router[router_index].output_status_h[WEST_BUFF] = USED;
                         packet_status[router[router_index].readbuff_h[swctr]].route[packet_list[router[router_index].readbuff_h[swctr]].hopcount] = router_index;    
                         packet_list[router[router_index].readbuff_h[swctr]].hopcount = packet_list[router[router_index].readbuff_h[swctr]].hopcount + 1;
                         router[router_index].readbuff_h[swctr] = INVALID_PACKET_INDEX;
                         router[router_index].inp_status_h[swctr] = FREE;
                         router[router_index].arb_buff[swctr].req[WEST_BUFF]  = FALSE_VAL;
                      :: skip        
                    fi;
 
                  /*  If X of destination address is equal to X of current router address, check Y Coordinates*/
                 :: packet_list[router[router_index].readbuff_h[swctr]].dest_index_x == router_id_x[router_index] ->
                    if
                       /* switch south bound if Y of destination address is less than Y of current router address*/
                      :: packet_list[router[router_index].readbuff_h[swctr]].dest_index_y < router_id_y[router_index] ->
                         if
                          :: router[router_index].arb_buff[swctr].ack[SOUTH_BUFF] == FALSE_VAL  ->
                             router[router_index].arb_buff[swctr].req[SOUTH_BUFF]  = TRUE_VAL; 
                          :: router[router_index].arb_buff[swctr].ack[SOUTH_BUFF] == TRUE_VAL && router[router_index].writebuff_h[SOUTH_BUFF]  == INVALID_PACKET_INDEX  ->
                             router[router_index].writebuff_h[SOUTH_BUFF]  = router[router_index].readbuff_h[swctr]; 
                             router[router_index].output_status_h[SOUTH_BUFF] = USED;
                             packet_status[router[router_index].readbuff_h[swctr]].route[packet_list[router[router_index].readbuff_h[swctr]].hopcount] = router_index;    
                             packet_list[router[router_index].readbuff_h[swctr]].hopcount = packet_list[router[router_index].readbuff_h[swctr]].hopcount + 1;
                             router[router_index].readbuff_h[swctr] = INVALID_PACKET_INDEX; 
                             router[router_index].inp_status_h[swctr] = FREE;
                             router[router_index].arb_buff[swctr].req[SOUTH_BUFF] = FALSE_VAL;
                          :: skip        
                         fi;
 
                       /* switch north bound if Y of destination address is greater than Y of current router address*/
                      :: packet_list[router[router_index].readbuff_h[swctr]].dest_index_y > router_id_y[router_index] ->
                         if
                           :: router[router_index].arb_buff[swctr].ack[NORTH_BUFF] == FALSE_VAL ->
                              router[router_index].arb_buff[swctr].req[NORTH_BUFF]  = TRUE_VAL;
                           :: router[router_index].arb_buff[swctr].ack[NORTH_BUFF] == TRUE_VAL && router[router_index].writebuff_h[NORTH_BUFF]  == INVALID_PACKET_INDEX ->
                              testvar = 5; router[router_index].writebuff_h[NORTH_BUFF]  = router[router_index].readbuff_h[swctr]; 
                              router[router_index].output_status_h[NORTH_BUFF] = USED;
                              packet_status[router[router_index].readbuff_h[swctr]].route[packet_list[router[router_index].readbuff_h[swctr]].hopcount] = router_index;    
                              packet_list[router[router_index].readbuff_h[swctr]].hopcount = packet_list[router[router_index].readbuff_h[swctr]].hopcount + 1;
                              router[router_index].readbuff_h[swctr] = INVALID_PACKET_INDEX; 
                              router[router_index].inp_status_h[swctr] = FREE;
                              router[router_index].arb_buff[swctr].req[NORTH_BUFF] = FALSE_VAL;
                           :: skip        
                         fi;

                     /*  If Y of destination address is equal to Y of current router address, current router is the destination router*/
                    :: packet_list[router[router_index].readbuff_h[swctr]].dest_index_y == router_id_y[router_index] ->
                        if
                         :: router[router_index].arb_buff[swctr].ack[NODE_BUFF] == FALSE_VAL -> 
                            router[router_index].arb_buff[swctr].req[NODE_BUFF]  = TRUE_VAL;
                         :: router[router_index].arb_buff[swctr].ack[NODE_BUFF] == TRUE_VAL && router[router_index].writebuff_h[NODE_BUFF]  == INVALID_PACKET_INDEX -> 
                            router[router_index].writebuff_h[NODE_BUFF]  = router[router_index].readbuff_h[swctr]; 
                            router[router_index].output_status_h[NODE_BUFF] = USED;
                            packet_status[router[router_index].readbuff_h[swctr]].route[packet_list[router[router_index].readbuff_h[swctr]].hopcount] = router_index;    
                            packet_list[router[router_index].readbuff_h[swctr]].hopcount = packet_list[router[router_index].readbuff_h[swctr]].hopcount + 1;
                            router[router_index].readbuff_h[swctr] = INVALID_PACKET_INDEX; 
                            router[router_index].inp_status_h[swctr] = FREE;
                            router[router_index].arb_buff[swctr].req[NODE_BUFF] = FALSE_VAL;
                         :: skip        
                        fi;
                     :: skip        
                    fi;    
                  :: skip        
                fi; 
               :: skip
             fi;

              swctr ++;
            :: else ->
              break;
            od;            

          do 
            :: arbctr < MAX_BUFF  ->
              /* perform i-th arbiter updates */
             /*  this will read swich_status_h[1] to swich_status_h[5]
                 and update output_status_g array. 
                 Note that you may need to use inp_output_connection_map_h 
                 array to copy this input to the input_status_g of 
                 some other router. */
              */
arb_state0:
             if
             :: router[router_index].arb_buff[EAST_BUFF].req[arbctr] == TRUE_VAL && router[router_index].arbitertoken[arbctr] == EAST_PRIORITY  ->
                router[router_index].arb_buff[EAST_BUFF].ack[arbctr]  = TRUE_VAL; 
                goto arb_state10;

             :: router[router_index].arb_buff[EAST_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arb_buff[EAST_BUFF].ack[arbctr]  == TRUE_VAL && router[router_index].arbitertoken[arbctr] == EAST_PRIORITY ->
                router[router_index].arb_buff[EAST_BUFF].ack[arbctr]  = FALSE_VAL; 
                router[router_index].arbitertoken[arbctr] = WEST_PRIORITY; 
                goto arb_state2;                

             :: router[router_index].arbitertoken[arbctr] == WEST_PRIORITY -> 
                goto arb_state2;            

             :: router[router_index].arbitertoken[arbctr] == NORTH_PRIORITY -> 
                goto arb_state4;            

             :: router[router_index].arbitertoken[arbctr] == SOUTH_PRIORITY -> 
                goto arb_state6;

             :: router[router_index].arbitertoken[arbctr] == NODE_PRIORITY -> 
                goto arb_state8;                        

             :: router[router_index].arb_buff[EAST_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arbitertoken[arbctr] == EAST_PRIORITY -> 
                router[router_index].arbitertoken[arbctr] = WEST_PRIORITY; 
                goto arb_state2;
             fi;
arb_state2:           

             if                
             :: router[router_index].arb_buff[WEST_BUFF].req[arbctr] == TRUE_VAL && router[router_index].arbitertoken[arbctr] == WEST_PRIORITY ->
                router[router_index].arb_buff[WEST_BUFF].ack[arbctr] = TRUE_VAL; 
                goto arb_state10;

             :: router[router_index].arb_buff[WEST_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arb_buff[WEST_BUFF].ack[arbctr] == TRUE_VAL && router[router_index].arbitertoken[arbctr] == WEST_PRIORITY ->
                router[router_index].arb_buff[WEST_BUFF].ack[arbctr]  = FALSE_VAL; 
                router[router_index].arbitertoken[arbctr] = NORTH_PRIORITY; 
                goto arb_state4;                

             :: router[router_index].arb_buff[WEST_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arbitertoken[arbctr] == WEST_PRIORITY -> 
                router[router_index].arbitertoken[arbctr] = NORTH_PRIORITY; 
                goto arb_state4;
             fi;
               

arb_state4:
            if                
             :: router[router_index].arb_buff[NORTH_BUFF].req[arbctr] == TRUE_VAL && router[router_index].arbitertoken[arbctr] == NORTH_PRIORITY ->
                router[router_index].arb_buff[NORTH_BUFF].ack[arbctr] = TRUE_VAL; 
                goto arb_state10;

             :: router[router_index].arb_buff[NORTH_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arb_buff[NORTH_BUFF].ack[arbctr] == TRUE_VAL&& router[router_index].arbitertoken[arbctr] == NORTH_PRIORITY ->
                router[router_index].arb_buff[NORTH_BUFF].ack[arbctr]  = FALSE_VAL; 
                router[router_index].arbitertoken[arbctr] = SOUTH_PRIORITY; 
                goto arb_state6;       
              
             :: router[router_index].arb_buff[NORTH_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arbitertoken[arbctr] == NORTH_PRIORITY -> 
                router[router_index].arbitertoken[arbctr] = SOUTH_PRIORITY; 
                goto arb_state6;       

           fi;


arb_state6:
            if                
             :: router[router_index].arb_buff[SOUTH_BUFF].req[arbctr] == TRUE_VAL && router[router_index].arbitertoken[arbctr] == SOUTH_PRIORITY ->
                router[router_index].arb_buff[SOUTH_BUFF].ack[arbctr] = TRUE_VAL; 
                goto arb_state10;

             :: router[router_index].arb_buff[SOUTH_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arb_buff[SOUTH_BUFF].ack[arbctr] == TRUE_VAL&& router[router_index].arbitertoken[arbctr] == SOUTH_PRIORITY ->
                router[router_index].arb_buff[SOUTH_BUFF].ack[arbctr]  = FALSE_VAL; 
                router[router_index].arbitertoken[arbctr] = NODE_PRIORITY; 
                goto arb_state8;
          
             :: router[router_index].arb_buff[SOUTH_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arbitertoken[arbctr] == SOUTH_PRIORITY -> 
                router[router_index].arbitertoken[arbctr] = NODE_PRIORITY; 
                goto arb_state8;
            fi;
              


arb_state8:
              
            if
                
             :: router[router_index].arb_buff[NODE_BUFF].req[arbctr] == TRUE_VAL && router[router_index].arbitertoken[arbctr] == NODE_PRIORITY ->
                router[router_index].arb_buff[NODE_BUFF].ack[arbctr]  = TRUE_VAL; 
                goto arb_state10;

             :: router[router_index].arb_buff[NODE_BUFF].req[arbctr]  == FALSE_VAL && router[router_index].arb_buff[NODE_BUFF].ack[arbctr]  == TRUE_VAL && router[router_index].arbitertoken[arbctr] == NODE_PRIORITY ->
                router[router_index].arb_buff[NODE_BUFF].ack[arbctr]  = FALSE_VAL; 
                router[router_index].arbitertoken[arbctr] = EAST_PRIORITY; 
                goto arb_state10;

             :: router[router_index].arb_buff[NODE_BUFF].req[arbctr] == FALSE_VAL && router[router_index].arbitertoken[arbctr] == NODE_PRIORITY -> 
                router[router_index].arbitertoken[arbctr] = EAST_PRIORITY; 
                goto arb_state10;

           fi;


arb_state10:
               arbctr++; 

            :: else ->
               break;
            od;            

          if  

              /* Check if packet is received and increment the counter */
              :: router[router_index].output_status_h[NODE_BUFF] == USED && router[router_index].writebuff_h[NODE_BUFF] != INVALID_PACKET_INDEX -> 
                 packet_status[router[router_index].writebuff_h[NODE_BUFF]].rcvctr = packet_status[router[router_index].writebuff_h[NODE_BUFF]].rcvctr + 1; 
                 packet_status[router[router_index].writebuff_h[NODE_BUFF]].packet_receive = TRUE_VAL;  
                 router[router_index].writebuff_h[NODE_BUFF] = INVALID_PACKET_INDEX ;
                 router[router_index].output_status_h[NODE_BUFF] = FREE;  
              :: skip;
          fi;


       /* topology mapping - copy packets to output ports */
          do 
            :: topologyctr < MAX_BUFF  ->
               if
                 :: router[router_index].output_status_h[topologyctr] == USED -> 
                    if 
                      :: router_id[router[router_index].input_output_connection_map_h[topologyctr]].inp_status_g[router[router_index].input_output_connection_port_h[topologyctr]]  != USED ->
                         router_id[router[router_index].input_output_connection_map_h[topologyctr]].readbuff_g[router[router_index].input_output_connection_port_h[topologyctr]] = router[router_index].writebuff_h[topologyctr];
                         router_id[router[router_index].input_output_connection_map_h[topologyctr]].inp_status_g[router[router_index].input_output_connection_port_h[topologyctr]] = USED;
                         router[router_index].writebuff_h[topologyctr] = INVALID_PACKET_INDEX; 
                         router[router_index].output_status_h[topologyctr]  = FREE;  
                  :: skip        
                   fi;
                 :: skip        
               fi;
              topologyctr ++;
            :: else ->
                break;
            od;            

           /* copy current state to global state */
          do 
            :: updtctr < MAX_BUFF  ->                 
               router_id[router_index].inp_status_g[updtctr] = router[router_index].inp_status_h[updtctr];
               router_id[router_index].readbuff_g[updtctr] = router[router_index].readbuff_h[updtctr];                        
               router_id[router_index].writebuff_g[updtctr] = router[router_index].writebuff_h[updtctr];                        
               router_id[router_index].arb_buff_g[updtctr].req_g[NODE_BUFF] = router[router_index].arb_buff[updtctr].req[NODE_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].req_g[EAST_BUFF] = router[router_index].arb_buff[updtctr].req[EAST_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].req_g[WEST_BUFF] = router[router_index].arb_buff[updtctr].req[WEST_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].req_g[NORTH_BUFF] = router[router_index].arb_buff[updtctr].req[NORTH_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].req_g[SOUTH_BUFF] = router[router_index].arb_buff[updtctr].req[SOUTH_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].ack_g[NODE_BUFF] = router[router_index].arb_buff[updtctr].ack[NODE_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].ack_g[EAST_BUFF] = router[router_index].arb_buff[updtctr].ack[EAST_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].ack_g[WEST_BUFF] = router[router_index].arb_buff[updtctr].ack[WEST_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].ack_g[NORTH_BUFF] = router[router_index].arb_buff[updtctr].ack[NORTH_BUFF];  
               router_id[router_index].arb_buff_g[updtctr].ack_g[SOUTH_BUFF] = router[router_index].arb_buff[updtctr].ack[SOUTH_BUFF];  
               router_id[router_index].arbitertoken_g[updtctr] = router[router_index].arbitertoken[updtctr];
               updtctr ++;
            :: else ->
                break;
           od;            

    } /* d_step */ 
  od;  /* infinite loop */

}

/*This process initializes packets and starts up the router */
proctype startup () 
{

 byte routerctr = 0; /* declared at top */
 byte portctr = 0; /* declared at top */
 byte ctr = 0; /* declared at top */

d_step{

 /* Intialize packet_list array */ 

    /* Node 0 data */
    /* node 0 has 2 packets */
    router[0].start_packet_index = 0;
    router[0].end_packet_index = 0;

   packet_list[0].dest_index_x = ROUTER_ID_8_x; 
   packet_list[0].dest_index_y = ROUTER_ID_8_y; 
   packet_list[0].pkt_index = 0;
   packet_list[0].src_index_x =ROUTER_ID_0_x;
   packet_list[0].src_index_y =ROUTER_ID_0_y;
   packet_list[0].hopcount=0;   


   packet_status[0].txctr = 0;
   packet_status[0].rcvctr = 0;
   packet_status[0].packet_send = FALSE_VAL;
   packet_status[0].packet_receive = FALSE_VAL;
   packet_status[0].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[0].route[8]= INVALID_ROUTER_INDEX;    

    /* Node 1 data */
    /* node 1 has 2 packets */

    router[1].start_packet_index = 1;
    router[1].end_packet_index = 1;

   packet_list[1].dest_index_x = ROUTER_ID_2_x; 
   packet_list[1].dest_index_y = ROUTER_ID_2_y; 
   packet_list[1].pkt_index = 1;
   packet_list[1].src_index_x =ROUTER_ID_1_x;
   packet_list[1].src_index_y =ROUTER_ID_1_y;
   packet_list[1].hopcount=0;


   packet_status[1].txctr = 0;
   packet_status[1].rcvctr = 0;
   packet_status[1].packet_send = FALSE_VAL;
   packet_status[1].packet_receive = FALSE_VAL;
   packet_status[1].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[1].route[8]= INVALID_ROUTER_INDEX;    


    /* Node 2 data */
    /* node 2 has 2 packets */

    router[2].start_packet_index = 2;
    router[2].end_packet_index = 2;

   packet_list[2].dest_index_x = ROUTER_ID_5_x; 
   packet_list[2].dest_index_y = ROUTER_ID_5_y; 
   packet_list[2].pkt_index = 2;
   packet_list[2].src_index_x =ROUTER_ID_2_x;
   packet_list[2].src_index_y =ROUTER_ID_2_y;
   packet_list[2].hopcount=0;



   packet_status[2].txctr = 0;
   packet_status[2].rcvctr = 0;
   packet_status[2].packet_send = FALSE_VAL;
   packet_status[2].packet_receive = FALSE_VAL;
   packet_status[2].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[2].route[8]= INVALID_ROUTER_INDEX;    


    /* Node 3 data */
    /* node 3 has 2 packets */

    router[3].start_packet_index = 3;
    router[3].end_packet_index = 3;

   packet_list[3].dest_index_x = ROUTER_ID_7_x; 
   packet_list[3].dest_index_y = ROUTER_ID_7_y; 
   packet_list[3].pkt_index = 3;
   packet_list[3].src_index_x =ROUTER_ID_3_x;
   packet_list[3].src_index_y =ROUTER_ID_3_y;
   packet_list[3].hopcount=0;



   packet_status[3].txctr = 0;
   packet_status[3].rcvctr = 0;
   packet_status[3].packet_send = FALSE_VAL;
   packet_status[3].packet_receive = FALSE_VAL;
   packet_status[3].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[3].route[8]= INVALID_ROUTER_INDEX;    


    /* Node 4 data */
    /* node 4 has 2 packets */

    router[4].start_packet_index = 4;
    router[4].end_packet_index  = 4;

   packet_list[4].dest_index_x = ROUTER_ID_8_x; 
   packet_list[4].dest_index_y = ROUTER_ID_8_y; 
   packet_list[4].pkt_index = 4;
   packet_list[4].src_index_x =ROUTER_ID_4_x;
   packet_list[4].src_index_y =ROUTER_ID_4_y;
   packet_list[4].hopcount=0;



   packet_status[4].txctr = 0;
   packet_status[4].rcvctr = 0;
   packet_status[4].packet_send = FALSE_VAL;
   packet_status[4].packet_receive = FALSE_VAL;
   packet_status[4].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[4].route[8]= INVALID_ROUTER_INDEX;    


    /* Node 5 data */
    /* node 5 has 2 packets */

    router[5].start_packet_index = 5;
    router[5].end_packet_index  = 5;

   packet_list[5].dest_index_x = ROUTER_ID_6_x; 
   packet_list[5].dest_index_y = ROUTER_ID_6_y; 
   packet_list[5].pkt_index = 5;
   packet_list[5].src_index_x =ROUTER_ID_5_x;
   packet_list[5].src_index_y =ROUTER_ID_5_y;
   packet_list[5].hopcount=0;



   packet_status[5].txctr = 0;
   packet_status[5].rcvctr = 0;
   packet_status[5].packet_send = FALSE_VAL;
   packet_status[5].packet_receive = FALSE_VAL;
   packet_status[5].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[5].route[8]= INVALID_ROUTER_INDEX;    

    /* Node 6 data */
    /* node 6 has 2 packets */

    router[6].start_packet_index = 6;
    router[6].end_packet_index  = 6;


   packet_list[6].dest_index_x = ROUTER_ID_3_x; 
   packet_list[6].dest_index_y = ROUTER_ID_3_y; 
   packet_list[6].pkt_index = 6;
   packet_list[6].src_index_x =ROUTER_ID_6_x;
   packet_list[6].src_index_y =ROUTER_ID_6_y;
   packet_list[6].hopcount=0;   


 
   packet_status[6].txctr = 0;
   packet_status[6].rcvctr = 0;
   packet_status[6].packet_send = FALSE_VAL;
   packet_status[6].packet_receive = FALSE_VAL;
   packet_status[6].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[6].route[8]= INVALID_ROUTER_INDEX;    

    /* Node 7 data */
    /* node 7 has 2 packets */

    router[7].start_packet_index = 7;
    router[7].end_packet_index = 7;

   packet_list[7].dest_index_x = ROUTER_ID_4_x; 
   packet_list[7].dest_index_y = ROUTER_ID_4_y; 
   packet_list[7].pkt_index = 7;
   packet_list[7].src_index_x =ROUTER_ID_7_x;
   packet_list[7].src_index_y =ROUTER_ID_7_y;
   packet_list[7].hopcount=0;


 
   packet_status[7].txctr = 0;
   packet_status[7].rcvctr = 0;
   packet_status[7].packet_send = FALSE_VAL;
   packet_status[7].packet_receive = FALSE_VAL;
   packet_status[7].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[7].route[8]= INVALID_ROUTER_INDEX;    

   /* Node 8 data */
    /* node 8 has 2 packets */

    router[8].start_packet_index = 8;
    router[8].end_packet_index = 9;

   packet_list[8].dest_index_x = ROUTER_ID_0_x; 
   packet_list[8].dest_index_y = ROUTER_ID_0_y; 
   packet_list[8].pkt_index = 8;
   packet_list[8].src_index_x =ROUTER_ID_8_x;
   packet_list[8].src_index_y =ROUTER_ID_8_y;
   packet_list[8].hopcount=0;


 
   packet_status[8].txctr = 0;
   packet_status[8].rcvctr = 0;
   packet_status[8].packet_send = FALSE_VAL;
   packet_status[8].packet_receive = FALSE_VAL;
   packet_status[8].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[8].route[8]= INVALID_ROUTER_INDEX;    


   packet_list[9].dest_index_x = ROUTER_ID_6_x; 
   packet_list[9].dest_index_y = ROUTER_ID_6_y; 
   packet_list[9].pkt_index = 8;
   packet_list[9].src_index_x =ROUTER_ID_8_x;
   packet_list[9].src_index_y =ROUTER_ID_8_y;
   packet_list[9].hopcount=0;


 
   packet_status[9].txctr = 0;
   packet_status[9].rcvctr = 0;
   packet_status[9].packet_send = FALSE_VAL;
   packet_status[9].packet_receive = FALSE_VAL;
   packet_status[9].route[0]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[1]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[2]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[3]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[4]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[5]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[6]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[7]= INVALID_ROUTER_INDEX;    
   packet_status[9].route[8]= INVALID_ROUTER_INDEX;    

   
   /* Intialize packet_list array, packets at each node */ 
 
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

  /* Define router mapping */
  router[0].input_output_connection_map_h[EAST_BUFF] = 1;
  router[0].input_output_connection_port_h[EAST_BUFF] = WEST_BUFF;

  router[0].input_output_connection_map_h[NORTH_BUFF] = 3;
  router[0].input_output_connection_port_h[NORTH_BUFF] = SOUTH_BUFF;

  router[0].input_output_connection_map_h[WEST_BUFF] = INVALID_ROUTER_INDEX;
  router[0].input_output_connection_port_h[WEST_BUFF] = INVALID_BUFF;

  router[0].input_output_connection_map_h[SOUTH_BUFF] = INVALID_ROUTER_INDEX;
  router[0].input_output_connection_port_h[SOUTH_BUFF] = INVALID_BUFF;



  router[1].input_output_connection_map_h[EAST_BUFF] = 2;
  router[1].input_output_connection_port_h[EAST_BUFF] = WEST_BUFF;

  router[1].input_output_connection_map_h[NORTH_BUFF] = 4;
  router[1].input_output_connection_port_h[NORTH_BUFF] = SOUTH_BUFF;

  router[1].input_output_connection_map_h[WEST_BUFF] = 0;
  router[1].input_output_connection_port_h[WEST_BUFF] = EAST_BUFF;

  router[1].input_output_connection_map_h[SOUTH_BUFF] = INVALID_ROUTER_INDEX;
  router[1].input_output_connection_port_h[SOUTH_BUFF] = INVALID_BUFF;




  router[2].input_output_connection_map_h[NORTH_BUFF] = 5;
  router[2].input_output_connection_port_h[NORTH_BUFF] = SOUTH_BUFF;

  router[2].input_output_connection_map_h[WEST_BUFF] = 1;
  router[2].input_output_connection_port_h[WEST_BUFF] = EAST_BUFF;

  router[2].input_output_connection_map_h[SOUTH_BUFF] = INVALID_ROUTER_INDEX;
  router[2].input_output_connection_port_h[SOUTH_BUFF] = INVALID_BUFF;

  router[2].input_output_connection_map_h[EAST_BUFF] = INVALID_ROUTER_INDEX;
  router[2].input_output_connection_port_h[EAST_BUFF] = INVALID_BUFF;




  router[3].input_output_connection_map_h[EAST_BUFF] = 4;
  router[3].input_output_connection_port_h[EAST_BUFF] = WEST_BUFF;

  router[3].input_output_connection_map_h[NORTH_BUFF] = 6;
  router[3].input_output_connection_port_h[NORTH_BUFF] = SOUTH_BUFF;

  router[3].input_output_connection_map_h[SOUTH_BUFF] = 0;
  router[3].input_output_connection_port_h[SOUTH_BUFF] = NORTH_BUFF;

  router[3].input_output_connection_map_h[WEST_BUFF] = INVALID_ROUTER_INDEX;
  router[3].input_output_connection_port_h[WEST_BUFF] = INVALID_BUFF;




  router[4].input_output_connection_map_h[WEST_BUFF] = 3;
  router[4].input_output_connection_port_h[WEST_BUFF] = EAST_BUFF;

  router[4].input_output_connection_map_h[EAST_BUFF] = 5;
  router[4].input_output_connection_port_h[EAST_BUFF] = WEST_BUFF;

  router[4].input_output_connection_map_h[NORTH_BUFF] = 7;
  router[4].input_output_connection_port_h[NORTH_BUFF] = SOUTH_BUFF;

  router[4].input_output_connection_map_h[SOUTH_BUFF] = 1;
  router[4].input_output_connection_port_h[SOUTH_BUFF] = NORTH_BUFF;




  router[5].input_output_connection_map_h[NORTH_BUFF] = 8;
  router[5].input_output_connection_port_h[NORTH_BUFF] = SOUTH_BUFF;

  router[5].input_output_connection_map_h[WEST_BUFF] = 4;
  router[5].input_output_connection_port_h[WEST_BUFF] = EAST_BUFF;

  router[5].input_output_connection_map_h[SOUTH_BUFF] = 2;
  router[5].input_output_connection_port_h[SOUTH_BUFF] = NORTH_BUFF;

  router[5].input_output_connection_map_h[EAST_BUFF] = INVALID_ROUTER_INDEX;
  router[5].input_output_connection_port_h[EAST_BUFF] = INVALID_BUFF;




  router[6].input_output_connection_map_h[EAST_BUFF] = 7;
  router[6].input_output_connection_port_h[EAST_BUFF] = WEST_BUFF;

  router[6].input_output_connection_map_h[SOUTH_BUFF] = 3;
  router[6].input_output_connection_port_h[SOUTH_BUFF] = NORTH_BUFF;

  router[6].input_output_connection_map_h[NORTH_BUFF] = INVALID_ROUTER_INDEX;
  router[6].input_output_connection_port_h[NORTH_BUFF] = INVALID_BUFF;

  router[6].input_output_connection_map_h[WEST_BUFF] = INVALID_ROUTER_INDEX;
  router[6].input_output_connection_port_h[WEST_BUFF] = INVALID_BUFF;




  router[7].input_output_connection_map_h[EAST_BUFF] = 8;
  router[7].input_output_connection_port_h[EAST_BUFF] = WEST_BUFF;

  router[7].input_output_connection_map_h[SOUTH_BUFF] = 4;
  router[7].input_output_connection_port_h[SOUTH_BUFF] = NORTH_BUFF;

  router[7].input_output_connection_map_h[WEST_BUFF] = 6;
  router[7].input_output_connection_port_h[WEST_BUFF] = EAST_BUFF;

  router[7].input_output_connection_map_h[NORTH_BUFF] = INVALID_ROUTER_INDEX;
  router[7].input_output_connection_port_h[NORTH_BUFF] = INVALID_BUFF;



  router[8].input_output_connection_map_h[WEST_BUFF] = 7;
  router[8].input_output_connection_port_h[WEST_BUFF] = EAST_BUFF;

  router[8].input_output_connection_map_h[SOUTH_BUFF] = 5;
  router[8].input_output_connection_port_h[SOUTH_BUFF] = NORTH_BUFF;

  router[8].input_output_connection_map_h[NORTH_BUFF] = INVALID_ROUTER_INDEX;
  router[8].input_output_connection_port_h[NORTH_BUFF] = INVALID_BUFF;

  router[8].input_output_connection_map_h[EAST_BUFF] = INVALID_ROUTER_INDEX;
  router[8].input_output_connection_port_h[EAST_BUFF] = INVALID_BUFF;



   do 
   :: ctr < MAX_ROUTERS ->
          do 
            :: portctr < MAX_BUFF  ->
                router_id[ctr].inp_status_g[portctr] = FREE;
                router_id[ctr].readbuff_g[portctr] = INVALID_PACKET_INDEX;
                router_id[ctr].writebuff_g[portctr] = INVALID_PACKET_INDEX;
                router_id[ctr].arb_buff_g[portctr].req_g[NODE_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].req_g[NORTH_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].req_g[EAST_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].req_g[WEST_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].req_g[SOUTH_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].ack_g[NODE_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].ack_g[NORTH_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].ack_g[EAST_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].ack_g[WEST_BUFF] = FALSE_VAL;
                router_id[ctr].arb_buff_g[portctr].ack_g[SOUTH_BUFF] = FALSE_VAL;
                router_id[ctr].arbitertoken_g[portctr] = EAST_PRIORITY ; 

                router[ctr].writebuff_h[portctr] = INVALID_PACKET_INDEX;
                router[ctr].arb_buff[portctr].req[NODE_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].req[NORTH_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].req[EAST_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].req[WEST_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].req[SOUTH_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].ack[NODE_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].ack[NORTH_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].ack[EAST_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].ack[WEST_BUFF] = FALSE_VAL;
                router[ctr].arb_buff[portctr].ack[SOUTH_BUFF] = FALSE_VAL;
                router[ctr].arbitertoken[portctr] = EAST_PRIORITY ; 
                portctr ++;
            :: else ->
                portctr =0;  break;
            od;   

      router[ctr].packet_base_index = router[ctr].start_packet_index;
      ctr ++;
   :: else ->  break;
   od;
  }      /* end of d_step */

   
  atomic{

   do 
   :: routerctr < MAX_ROUTERS ->
        run router_node(routerctr);
         routerctr ++;
   :: else ->
      break;
   od;
    }     /* end of atomic */


}

init {

  run startup();

}
