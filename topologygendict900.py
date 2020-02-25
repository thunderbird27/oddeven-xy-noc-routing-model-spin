i = 0 #row
j = 0 #column

no = 0 # router number

rowval = 30
colval = 30
routval = 900

filename2 ="topologydef.txt"
mapad = open(filename2,'w')

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

