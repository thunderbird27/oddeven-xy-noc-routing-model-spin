i = 0 #row
j = 0 #column

no = 0 # router number

rowval = 30
colval = 30
routval =900

filename2 ="rouaddef.txt"
mapad = open(filename2,'w')

routeraddr = { }
while j < colval:

   while i < colval:
      a = "ROUTER_ID_"+str(no)+"_x"
      routeraddr[a] = str(i)
      print a,i
      b = "ROUTER_ID_"+str(no)+"_y"
      routeraddr[b] = str(j)
      print b, j
      data1 = "#define  "+ a +" " + str(i)
      mapad.write(data1)
      datan = '\n'
      mapad.write(datan)
      data1 = "#define  "+ b +" " + str(j)
      mapad.write(data1)
      datan = '\n'
      mapad.write(datan)

      i = i + 1
      no = no + 1          
   j = j +1
   i = 0
   
print len(routeraddr)

print "values in router addr"
for keys, items in routeraddr.items():
      print "keys",keys
      print "items" ,items

      
idex = 0
while idex <= 899:

  print idex  
  frx = "ROUTER_ID_"+str(idex)+"_x"
  fry = "ROUTER_ID_"+str(idex)+"_y"
  print routeraddr[frx],routeraddr[fry]  
  idex = idex + 1   


filename2 ="mapad.txt"
mapada = open(filename2,'w')

for keys,itms in routeraddr.items():
    a = keys.split('_')
    print a,a[2],a[3] 

   
    data1 = "router_id_"+a[3]+"[" + a[2]+ "] = "+ keys +";"
    mapada.write(data1)
    datan = '\n'
    mapada.write(datan)

  
mapad.close()
mapada.close()
