"""
Contains the function push_down, which is used by intersection7.py.

Not sure if there is a good reason for this to be in its own file.
"""

import sys
if "." not in sys.path: sys.path.insert(0,".")

try:
    from TautRing3 import *
    from sage.all import *
except ImportError:
    pass
    
def push_down(psi_exp, g, n):
    """
    Pushes down the psi_classes via forgetful maps as far as possible, using the string equation and the formula from [AC].  Returns a polynomial in psi and kappa classes.
    """
    #print "recieved", psi_exp, g, n
    psi_exp = [expon for expon in psi_exp if expon != 0]
    if len(psi_exp) == n:
        #use AC formula
        if g == 0:
            raise Exception( "???")
        elif g == 1:
            raise Exception( "???")
        else:
            M = Mgn(g, 0)
        result = 0
        for p in SetPartitions(xrange(len(psi_exp))):            
            result += prod([factorial(len(s) - 1) for s in p])*prod([kappa_class(M, sum([psi_exp[i] - 1 for i in s])) for s in p])
        return result
    else:
        #do string equation
        value = 0
        for i in xrange(len(psi_exp)):
            a = list(psi_exp)
            a[i] -= 1
            value += push_down(a, g, n - 1)
        return value
        
        
        

    
    
    
