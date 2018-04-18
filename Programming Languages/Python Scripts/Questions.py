"""
Procedures for F28PL
By Antonio Gargaro
"""

def mult1(List =[]):
    x=1
    for i in range(len(List)):
       x = x*List[i]
    return x

def mult2(list = []):
    if len(list) == 1:
        return list[0]

    return list[0] * mult2(list[1:])

def mult3(list = []):
    from functools import reduce
    return reduce(lambda x, y: x * y, list)

def multpoly(list = []):
    if type(list[0]) == str:
        x = ""
        for i in range(len(list)):
            x += list[i]
        return x

    if type(list[0]) == int:
        x=1
        for i in range(len(list)):
           x = x*list[i]
        return x

    if type(list[0]) == type([]):
        x=[]
        for i in range(len(list)):
            for j in range (len(list[i])):
                x.append(list[i][j])
        return x

def flatten(list = []):
    x = []
    for i in range(len(list)):
        if type(list[i]) != type([]):
            x.append(list[i])
        else:
            temp = (flatten(list[i]))
            for i in range(len(temp)):
                x.append(temp[i])
    return x

def factors(n):
    primes = []
    x = 2
    while x*x <= n:
        while (n % x) == 0: #checks for prime
            primes.append(x)
            n //= x    #Floor Division
        if(x > 2):     #Only odd numbers used
            x+=2
        else:
            x += 1
    if n > 1:
        primes.append(n)
    return primes

def largest(list = []):
    largest = 0
    for i in range(len(list)):
        if(list[i] > largest):
            largest = list[i]
    return largest

def largest_factor(n):
    return largest(factors(n))

def firstbigfib(n):
    fib = [0,1]
    i=1
    while(n != len(str(fib[i]))):
        fib.append(fib[i]+fib[i-1])
        i += 1
    return fib[i]

def firstbigf(n, f):
    i = 1
    x = f(i)
    while n > len(str(x)):
        i += 1
        x = f(i)
    return i

def triples():
    x = 1
    y = 2
    while(x > 0):
        yield (x*x)+(y*y)
        x +=1
        y+=1

def evens(n):
    f = lambda x: (x % 2 == 0)
    return [x for x in list(range(n*2)) if f(x)]

def div3(l = []):
    f = lambda x: (x % 3 == 0)
    return [x for x in l if f(x)]

def zip(l1 = [], l2 = []):
    return[(l1[i], l2[i]) for i in range(len(l1))]

def sandp ():
    i = 9702

    squares = [x * x
               for x in range(i)]
    pentagonals = [x * (3 * x - 1) // 2
                   for x in range(i)]



    return [x for x in squares if (x in pentagonals)]

def nest(n):        #keeps nesting lists into lists n times
    if (n == 0):
        return []
    else:
        return [nest(n-1)]

def unnest(n):      #keeps unnesting lists and tallying total
    if (n == []):
        return 0
    else:
        return 1 + unnest(n[0])

def addition(l1, l2):
    if (l2 == []):
        return l1
    else:
        return addition([l1], l2[0]) #nests l1 while unnests l2

def multiplication(l1, l2):
    if (l1 == [] or l2 == []):
        return 0
    elif (l2 == [[]]):
        return l1
    else:
        ltemp = l2
        while ltemp != [[]]:
            l1 = addition(l1, l2)
            ltemp = ltemp[0]

    return l1
