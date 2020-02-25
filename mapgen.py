rowval = 30
colval = 30
routval = 900

i = 0
graph1={}

a1= "graph1 = {"
print a1

routeraddr = { }
while i < routval:
   m = 99
   n = 99
   if i == 0 :
            c = i + 1
            d = i + 30
            a2 = "R"+str(i)+":{x:["+"R"+str(c)+"],"+"y:[R"+str(d)+"]},"
            
            s = "R"+str(i)
            s1 = []
            s2 = []
            val1= "R"+str(c)
            val2 = "R"+str(d)
            s1.append(val1)
            s2.append(val2)
            graph1.setdefault(s, {})['x'] = s1
            graph1.setdefault(s, {})['y'] = s2                                       
            
            

   elif i == 29:
            c = i - 1
            d = i + 30
            s = "R"+str(i)
            s1 = []
            s2 = []
            val1= "R"+str(c)
            val2 = "R"+str(d)
            s1.append(val1)
            s2.append(val2)
            graph1.setdefault(s, {})['x'] = s1
            graph1.setdefault(s, {})['y'] = s2
            
   elif i > 0 and i < 29:
            c = i + 1
            e = i - 1
            d = i + 30
            s = "R"+str(i)
            s1 = []
            s2 = []
            val1= "R"+str(c)
            val2 = "R"+str(d)
            val3 = "R"+str(e)
            s1.append(val1)
            s1.append(val3)
            s2.append(val2)
            graph1.setdefault(s, {})['x'] = s1
            graph1.setdefault(s, {})['y'] = s2

            
   elif i == 870 :
            c = i + 1
            d = i - 30
            s = "R"+str(i)
            s1 = []
            s2 = []
            val1= "R"+str(c)
            val2 = "R"+str(d)
            s1.append(val1)
            s2.append(val2)
            graph1.setdefault(s, {})['x'] = s1
            graph1.setdefault(s, {})['y'] = s2


   elif  i == 899:
            c = i - 1
            d = i - 30
            s = "R"+str(i)
            s1 = []
            s2 = []
            val1= "R"+str(c)
            val2 = "R"+str(d)
            s1.append(val1)
            s2.append(val2)
            graph1.setdefault(s, {})['x'] = s1
            graph1.setdefault(s, {})['y'] = s2


   elif i > 870 and i < 899:
            c = i + 1
            e = i - 1
            d = i - 30
            s = "R"+str(i)
            s1 = []
            s2 = []
            val1= "R"+str(c)
            val2 = "R"+str(d)
            val3 = "R"+str(e)
            s1.append(val1)
            s1.append(val3)
            s2.append(val2)
            graph1.setdefault(s, {})['x'] = s1
            graph1.setdefault(s, {})['y'] = s2

   elif i > 0 and i < 899:
            m = i % 300
            n = (i + 1) % 30
            if m !=0 and n!=0:
               c = i + 1
               e = i - 1
               d = i - 30
               f = i + 30
               s = "R"+str(i)
               s1 = []
               s2 = []
               val1= "R"+str(c)
               val2 = "R"+str(d)
               val3 = "R"+str(e)
               val4 = "R"+str(f)
               s1.append(val1)
               s1.append(val3)
               s2.append(val2)
               s2.append(val4)
               graph1.setdefault(s, {})['x'] = s1
               graph1.setdefault(s, {})['y'] = s2
               

            elif n == 0:
               c = i - 1            
               d = i - 30
               f = i + 30
               s = "R"+str(i)
               s1 = []
               s2 = []
               val1= "R"+str(c)
               val2 = "R"+str(d)               
               val4 = "R"+str(f)
               s1.append(val1)               
               s2.append(val2)
               s2.append(val4)
               graph1.setdefault(s, {})['x'] = s1
               graph1.setdefault(s, {})['y'] = s2                           
               n = 99

            elif m == 0 :
               c = i + 1            
               d = i - 30
               f = i + 30
               s = "R"+str(i)
               s1 = []
               s2 = []
               val1= "R"+str(c)
               val2 = "R"+str(d)               
               val4 = "R"+str(f)
               s1.append(val1)               
               s2.append(val2)
               s2.append(val4)
               graph1.setdefault(s, {})['x'] = s1
               graph1.setdefault(s, {})['y'] = s2
               m = 99

   i = i + 1

# print graph1 
i = 0
while i < len(graph1):
  
   s = "R" + str(i)
   print s,graph1[s]
   #for keys, r in graph1.items():
      #if keys == s :
          #print keys,r
   i = i + 1


filename2 ="mapid.txt"
mapid = open(filename2,'w')


for keys,itms in graph1.items():
    for k,it in itms.items():
        newstr = keys[1:]
        keyR = int(newstr)
        if k == 'x':
           if len(it) == 2: 
              newit0 = it[0] 
              newit1 = it[1]
              R0 = int(newit0[1:])
              R1 = int(newit1[1:])
              if R0 < R1:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[WEST_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [WEST_BUFF] = EAST_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[EAST_BUFF] = "+str(R1)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [EAST_BUFF] = WEST_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
              if R1 < R0:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[WEST_BUFF] = "+str(R1)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [WEST_BUFF] = EAST_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[EAST_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [EAST_BUFF] = WEST_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)                  
           if len(it) == 1: 
              newit0 = it[0]
              R0 = int(newit0[1:])
              if R0 < keyR:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[WEST_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [WEST_BUFF] = EAST_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[EAST_BUFF] = INVALID_ROUTER_INDEX;"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [EAST_BUFF] = INVALID_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
              if R0 > keyR:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[EAST_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [EAST_BUFF] = WEST_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[WEST_BUFF] = INVALID_ROUTER_INDEX;"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [WEST_BUFF] = INVALID_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)

        if k == 'y':
           if len(it) == 2: 
              newit0 = it[0] 
              newit1 = it[1]
              R0 = int(newit0[1:])
              R1 = int(newit1[1:])
              if R0 < R1:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[SOUTH_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [SOUTH_BUFF] = NORTH_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[NORTH_BUFF] = "+str(R1)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [NORTH_BUFF] = SOUTH_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
              if R1 < R0:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[SOUTH_BUFF] = "+str(R1)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [SOUTH_BUFF] = NORTH_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[NORTH_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [NORTH_BUFF] = SOUTH_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)                  
           if len(it) == 1: 
              newit0 = it[0]
              R0 = int(newit0[1:])
              if R0 < keyR:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[SOUTH_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [SOUTH_BUFF] = NORTH_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[NORTH_BUFF] = INVALID_ROUTER_INDEX;"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [NORTH_BUFF] = INVALID_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
              if R0 > keyR:
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[NORTH_BUFF] = "+str(R0)+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [NORTH_BUFF] = SOUTH_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_map_h[SOUTH_BUFF] = INVALID_ROUTER_INDEX;"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)
                  data1 = "router[" + newstr+ "].input_output_connection_port_h [SOUTH_BUFF] = INVALID_BUFF"+";"
                  mapid.write(data1)
                  datan = '\n'
                  mapid.write(datan)



mapid.close()
