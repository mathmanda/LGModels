"""
This module contains:

ModuliSpace
    Methods:
        RRD
        dim
        divisors_by_genus_marks
        all_boundary_concave
        drewspace
        class_list 
        _Class_Poly_Ring
        psiplus
        psiminus
        chern_chars
        chern_classes
        Dth_chern_class_total
        correlator
        intersect
        
    Data attributes:
        vert


TODO:
    Document!
    Add more tests, including all known from FJR and KS papers


AUTHORS:

    - Amanda Francis (2012) Initial design and implementation
    - Tyler Jarvis (2012 September 25) streamlined, some optimization:
                  Replaced classstring by class_list
                  Made _Class_Poly_Ring a multivariate ring instead of a nest of univariates
                  Tightened up to improve memory usage and speed
                               chern_classes 
                               Dth_chern_class_total 
                               correlator
                               intersect
   
"""
# if not __name__ == '__main__':  # i.e. if this is being read as a load or 
                                # attach.
try:
    from sage.all import *
except ImportError:
    print( "Didn't import Sage!!!")

import sys
if "." not in sys.path: sys.path.insert(0,".")
    
from intersection_ui import *
from LazyAttr import lazy_attr            
import warnings

class ModuliSpace:

    """
    Class that represents the moduli space corresponding to a certain correlator.
    It also contains methods for computing various cohomology classes.
    
    CONSTRUCTOR:
    - ``FJRW`` -- an FJRW ring
    - ``corr`` -- list of FJRW basis elements
    - ``g`` -- genus, defaults to zero
    
    EXAMPLES:
    First create the FJRW Ring and select the basis elements and genus::
    
        sage: from LGModels import * 
        sage: W = QSingularity.create('l223') 
        sage: G = SymmetryGroup(W,'J')
        sage: A = FJRWRing(G,print_basis=False)
        sage: a = [A[2], A[2],A[7],A[11],A[12]]
        sage: Mbar = ModuliSpace(A,a)
        
        sage: Mbar2 = ModuliSpace(A,a,g=1)
        
    
   
    """
    def __init__(self, FJRW, corr, g=0):
        """ Constructor -- see class documentation."""
        self.corrvec = corr
        self.FJRW = FJRW
        self.genus = g
        # Correlator length
        self.n = len(corr)
        # Number of variables
        self.N = len(FJRW.singularity.q)

    ##TJ: lazy_attr breaks this code for some reason--I don't know why.    
    #@lazy_attr   
    def RRD(self):
        """ 
        Finds D := -sum of indices of L_i  using Riemann-Roch Theorem
        
        Caveat: RRD returns a rational---not type integer.

        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.RRD()
            2

            sage: W = QSingularity.create('c33') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[3],A[3]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.RRD()
            0


        
        
        """
        N = self.N
        g = self.genus
        a = self.corrvec
        ##TJ: replaced loop with sum of list comprehension
        D = N*(g-1) - sum([self.FJRW.line_bundle_degrees(a, g)[i] 
                           for i in range(N)])
        ##TJ Ensure D is an integer and of type integer
        if not D.is_integral():
            raise ValueError('D = {0} is not integral'.format(D))
        else: 
            D = D.floor()  #make it of type integer
        return D  

    #@lazy_attr    
    def dim(self):
        """
        Gives dimension of the moduli space

        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.dim()
            2

            sage: W = QSingularity.create('c33') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[3],A[3]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.dim()
            0

        
        """
        return 3*self.genus - 3 + self.n
    
    
    # Used in chern_chars. Lazy Attribute?
    def divisors_by_genus_marks(self):
        """
        Returns a list of reducible, degree-one boundary classes, 
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.divisors_by_genus_marks()
            [[0, [1, 5], 0, [2, 3, 4]], [0, [1, 4], 0, [2, 3, 5]], [0, [1, 4, 5], 0, [2, 3]], 
            [0, [1, 3], 0, [2, 4, 5]], [0, [1, 3, 5], 0, [2, 4]], [0, [1, 3, 4], 0, [2, 5]], 
            [0, [1, 2], 0, [3, 4, 5]], [0, [1, 2, 5], 0, [3, 4]], [0, [1, 2, 4], 0, [3, 5]], 
            [0, [1, 2, 3], 0, [4, 5]]]     
        
        
        ..WARNING::
            Doesn't pinch loops
            
        .. TODO::
        
            Add loop pinching
        
        
        """
        n = self.n
        g = self.genus
        redbound = []
        marks = []
        #create a list of marks:
        for p in range(n):
            marks.append(n - p)
        if n != 0:
            #Find subsets of marks containing 1 (to do this remove 1 and look at subsets)
            first_mark_list = [marks.pop()]            
            #possible genera for component with 1
            for g1 in range(0, g + 1):
                #possible subsets of marks
                for p in subsets(marks):
                    p.reverse()
                    r_marks = list(first_mark_list + p)
                    #both components must be stable:
                    if 3*g1 - 3 + len(r_marks) + 1 >= 0 and 3*(g - g1) - 3 + n - len(r_marks) + 1 >= 0:
                        r_marks.sort()
                        l_marks = list(set(marks).difference(set(r_marks)))
                        l_marks.sort()
                        redbound.append([g1, r_marks,g-g1,l_marks])
        else: #n == 0
            print( "Error: No marked points?" )   
        return redbound
        

    def all_boundary_concave(self, verbose = False):
        """
        Return true if all boundary divisors are concave
        Print list of non-concave boundaries if verbose = True
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.all_boundary_concave()
            True


            sage: a = [A[2], A[3],A[5],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.all_boundary_concave(verbose=True)
            bad vertex [marks, edges] [[1, 3], [(6/13, 1/13, 11/13)]]
            deg(L_1)= 0
            False

        
        """
##TJ Edited to check that edges do not have zero group elements.
        
        applies = True
        boundaries = self.all_deg_bdry_graphs()
        a = self.corrvec
        A = self.FJRW
        LB = A.line_bundle_degrees(a)
        J = A[1].sector
        Zero = J*0 #surely there is a better way to build zero group el
        if applies == True:
            for b in boundaries:
                for node in b: #vertices of the graph
                    marks = node[0] #marks
                    edges = node[1] #group elements labeling interior half-edges
                    if Zero not in edges: 
                        '''
                        If an edge is labeled zero, then each LB
                        behaves as if it were one line bundle on the
                        curve obtained by deleting the edge.  Since we
                        check that case elsewhere, skip it now.
                        '''
                        k = len(marks) + len(edges)            
                        for j in range(len(LB)):
                            zero_edge = False
                            #this line bndle not fail the zero-edge check yet.
                            lbbdry = J[j]
                            for mark in marks:
                                lbbdry -= a[mark - 1].sector[j]
                            for gp in edges:
                                zero_edge = zero_edge or gp[j] == 0
                                lbbdry -= gp[j]
                            if lbbdry >= 0 and not zero_edge:  
                                applies = False
                                if verbose == True:
                                    #print "bad boundary graph", b
                                    print("bad vertex [marks, edges]", node)
                                    print("deg(L_" + str(j) + ")=", lbbdry)
        return applies

    #@lazy_attr
    def drewspace(self):
        """
        Returns the space (with cohomology classes) in Drew's intersection code
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: M = Mbar.drewspace()
            sage: M
            Mbar_0_5
            sage: M.classes
            [psi1, psi2, psi3, psi4, psi5, ka1, ka2, 0, Dg0m1_2, Dg0m1_3, Dg0m1_4, Dg0m1_5, 
            Dg0m1_2_3, Dg0m1_2_4, Dg0m1_2_5, Dg0m1_3_4, Dg0m1_3_5, Dg0m1_4_5]
        
        """
        sp = space(self.genus, self.n, namespace = globals(), print_classes=false)
        return sp
    
    #@lazy_attr
    def classstring(self):
        """
        Returns a string of all relevant cohomology classes
        
        TJ: Don't know why you want a string instead of a list of strings.
            Deprecated.  Replaced by class_list
         
        """
###################################################
        warnings.warn("self.classstring() is deprecated and will be removed in a future version of TheCode. Use self.class_list() instead.", stacklevel = 3)
################################################### 
        str_list = ""
        #Pulls list of cohomology classes from Drew's code
        vec = self.drewspace().classes
        #Remove any trivial cohomology classes
        while 0 in vec:
            vec.remove(0)
        #Create a string which lists all of the important classes
        for item in vec:
            str_list += repr(item) + ", "
        return str_list




    #@lazy_attr
    def class_list(self):
        """
        Returns a list of all relevant cohomology class names (strings)
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.class_list()
            ['psi1', 'psi2', 'psi3', 'psi4', 'psi5', 'ka1', 'ka2', 'Dg0m1_2', 'Dg0m1_3', 'Dg0m1_4', 'Dg0m1_5', 'Dg0m1_2_3', 'Dg0m1_2_4', 'Dg0m1_2_5', 'Dg0m1_3_4', 'Dg0m1_3_5', 'Dg0m1_4_5']
                
        """
        #Pulls list of cohomology classes from Drew's code
        vec = self.drewspace().classes
        #Remove any trivial cohomology classes
        while 0 in vec:
            vec.remove(0)
        #Create a string which lists all of the important classes
        str_list = [repr(x) for x in vec] 
        return str_list


    #@lazy_attr    
    def _Class_Poly_Ring(self):
        """
        Return a polynomial ring in classes of self.drewspace()
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar._Class_Poly_Ring()
            Multivariate Polynomial Ring in psi1, psi2, psi3, psi4, psi5, ka1, ka2, Dg0m1_2, Dg0m1_3, Dg0m1_4, Dg0m1_5, Dg0m1_2_3, Dg0m1_2_4, Dg0m1_2_5, Dg0m1_3_4, Dg0m1_3_5, Dg0m1_4_5 over Number Field in I with defining polynomial x^2 + 1            
        
            sage: W = QSingularity.create('c33') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[3],A[3]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar._Class_Poly_Ring()
            Multivariate Polynomial Ring in psi1, psi2, psi3 over
            Number Field in I with defining polynomial x^2 + 1
 
        """
        a = sqrt(-1)
        R = QQ[a]
        #R = CC
        names = self.class_list()
        reset(names)
        var(names)
        R = PolynomialRing(R,names)
        return R

    
    def psiplus(self, K, string = True, reduce = True):
        """
        Uses relation (below) to convert psiplus to a polynomial in boundary classes,
        psiplus = sum_{a, b \notin I} Delta_I
        
        Actually - this method comes before pushing forward.
        #See "Witten's D_4 integrable hierarchies conjecture" by Fan, Jarvis, Merrell, Ruan
        #Sub-Lemma 5.3
        
        INPUT 
        - ``K`` -- A list of marks or "cut", including 1
        - ``string`` -- returns strings instead of lists if True
        - ``reduce`` -- uses the fact that all psi classes are equal on M_0_4 instead of
                        the regular method
        
        ..WARNING::
            This only works for genus = 0
            
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.psiplus([1,2,3])
            'psi1'
            
            sage: Mbar.psiplus([1,2,3], reduce = False)
            'Dg0m1_4_5'           
            
            sage: Mbar.psiplus([2,3,4], reduce = False)
            Error:  K should contain 1

            
        """
        K.sort()
        if K[0] != 1:
            print("Error:  K should contain 1")
        elif len(K) < 3 and string == True:
            return "0"
        elif len(K) < 3:
            return 0
        elif reduce == True and len(K) == 3 and string == True:
            return "psi1"
        else:
            #Make a string representation of K, for the code.
            stK = "Dg0m" + str(K[0])
            for i in range(1, len(K)):
                stK += "_" + str(K[i])
            
            totalmarks = [i + 1 for i in range(self.n)]  # all marks
            Kcomp = set(totalmarks).difference(set(K)) #complement of K
            sumpieces = [] #list of things in the sum
            sumstring = ""
            # Find subsets of K which do not contain 1 = K[0], K[1], or K[2]
            Ksub = [K[i] for i in range(3, len(K))]  
            for p in subsets(Ksub):
                p.append(1)
                setp = set(p)
                Union = list(setp.union(Kcomp))  # I union K^c
                Union.sort()
                # return strings (to be put in Drew's code):
                if string == True:
                    #Second part of sum in Sub-Lemma 5.3
                    st1 = "Dg0m" + str(Union[0])
                    Union.remove(Union[0])
                    for m in Union:
                        st1 += "_" + str(m)
                    sumpieces.append(st1)
                    #sumpieces.append(st1 + "*" + stK)
                    
                    #First part of sum in Sub-Lemma 5.3
                    p.append(K[1])
                    p.append(K[2])  #I
                    p.sort()
                    if p != K:
                        st1 = "Dg0m" + str(p[0])
                        for m in range(1, len(p)):
                            st1 += "_" + str(p[m])
                        sumpieces.append(st1)
                        #sumpieces.append(st1 + "*" + stK)
                        
                #return lists of marks (easier to manipulate):
                else:
                    #Second part of sum in Sub-Lemma 5.3
                    sumpieces.append(Union)
                    #sumpieces.append([K, Union])
                    #First part of sum in Sub-Lemma 5.3
                    if len(p) > 1:
                        p.append(K[1])
                        p.append(K[2])
                        #sumpieces.append([K, p])
                        sumpieces.append(p)
            if string == True:
                #Create one string for the sum:    
                sumstring += sumpieces[0]
                for i in range(1, len(sumpieces)):
                    sumstring += " + " + sumpieces[i]
                return sumstring
            else:
                return sumpieces
             
    def psiminus(self, K, string = True, reduce=True):
        """
        Uses relation (below) to convert psiplus to a polynomial in boundary classes, then pushforward
        psiminus = sum_{a, b \notin I} Delta_I
        
        See "Witten's D_4 integrable hierarchies conjecture" by Fan, Jarvis, Merrell, Ruan
        Sub-Lemma 5.3
        
        INPUT 
        - ``K`` -- A list of marks or "cut", including 1
        - ``string`` -- returns strings instead of lists if True
        - ``reduce`` -- uses the fact that all psi classes are equal on M_0_4 instead of
                        the regular method
        
        WARNING:  
            This only works for genus = 0
            
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.psiminus([1,5])
            'psi2'
            
            sage: Mbar.psiminus([1,5], reduce = False)
            'Dg0m1_4_5'            
            
            sage: Mbar.psiminus([2,5], reduce = False)
            Error:  K should contain 1


            
        """
        #K should contain 1
        K.sort()
        if K[0] != 1:
            print("Error:  K should contain 1")
        #Check if |K^c| < 3
        elif self.n - len(K) < 3 and string == True:
            return "0"
        elif self.n - len(K) < 3:
            return 0
        elif reduce == True and self.n - len(K) == 3 and string == True:
            totalmarks = [i + 1 for i in range(self.n)]  # all marks
            Kcomp = set(totalmarks).difference(set(K)) #complement of K
            return "psi" + str(list(Kcomp)[0])
            print("psiminus", K, "psi" + str(list(Kcomp)[0]))
        else:
            #Make a string representation of K, for the code.
            stK = "Dg0m" + str(K[0])
            for i in range(1, len(K)):
                stK += "_" + str(K[i])
            
            totalmarks = [i + 1 for i in range(self.n)]  # all marks
            Kcomp = list(set(totalmarks).difference(set(K))) #complement of K
            sumpieces = [] #list of things in the sum
            sumstring = "" # string - the whole sum
            #Find nonempty subsets of Kcomp, not containing the first two elements of Kcomp
            Kcomp.remove(Kcomp[0])
            Kcomp.remove(Kcomp[0])
            for p in subsets(Kcomp):
                if len(p) > 0:
                    setp = set(p)
                    Union = list(setp.union(set(K)))  # I union K
                    Union.sort()
                    
                    # return strings (to be put in Drew's code):
                    if string == True:
                        st1 = "Dg0m" + str(Union[0])
                        for m in range(1, len(Union)):
                            st1 += "_" + str(Union[m])
                        sumpieces.append(st1)
                        #sumpieces.append(st1 + "*" + stK)
                    #return lists of marks (easier to manipulate):
                    else:
                        sumpieces.append(Union)
                        #sumpieces.append([K, Union])
            if string == True:  #what to return for string case:
                    if len(sumpieces) > 0:
                        sumstring += sumpieces[0]
                        for i in range(1, len(sumpieces)):
                            sumstring += " + " + sumpieces[i]
                        return sumstring
                    else:
                        return "0"
            else:  #What to return otherwise:
                    return sumpieces
    
    def chern_chars(self, k, shortcut = False):
        """
        Returns a vector with chern character coefficients (up to dim of moduli space)
        corresponding to the ch_i(R^dot pi_* L_k).
    
        INPUT:
    
        - ``k`` -- an integer: the index of the Line Bundle
        - ``shortcut``-- if True uses rank of vector bundle 
                         to reduce number of necessary computations

        OUTPUT: 
        
        - ``ch`` -- chern character coefficients: a list of polynomials in the 
            relevant kappa, psi, and boundary classes
        
        TODO::
            Find better example--
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.chern_chars(0)
            [-11/26, -83/2028*Dg0m1_2 + 1/12*Dg0m1_2_3 - 11/2028*Dg0m1_2_4 + 37/2028*Dg0m1_2_5
            + 97/2028*Dg0m1_3 - 11/2028*Dg0m1_3_4 - 47/2028*Dg0m1_3_5 - 47/2028*Dg0m1_4 + 
            97/2028*Dg0m1_4_5 - 11/2028*Dg0m1_5 - 47/2028*ka1 + 71/2028*psi1 + 71/2028*psi2 
            - 37/2028*psi3 + 71/2028*psi4 + 47/2028*psi5, 7/4394*Dg0m1_2*psi3 
            + 35/4394*Dg0m1_2_4*psi1 + 33/4394*Dg0m1_2_5*psi1 - 11/2197*Dg0m1_3*psi2 
            - 35/4394*Dg0m1_3_4*psi1 - 15/2197*Dg0m1_3_5*psi1 - 15/2197*Dg0m1_4*psi2 
            - 11/2197*Dg0m1_4_5*psi1 - 35/4394*Dg0m1_5*psi2 - 10/2197*psi1^2 - 10/2197*psi2^2 
            + 33/4394*psi3^2 + 10/2197*psi4^2 + 15/2197*psi5^2 + 15/2197*ka2]
            sage: Mbar.chern_chars(0,shortcut = True)
            [-11/26, -83/2028*Dg0m1_2 + 1/12*Dg0m1_2_3 - 11/2028*Dg0m1_2_4 + 37/2028*Dg0m1_2_5 
            + 97/2028*Dg0m1_3 - 11/2028*Dg0m1_3_4 - 47/2028*Dg0m1_3_5 - 47/2028*Dg0m1_4 
            + 97/2028*Dg0m1_4_5 - 11/2028*Dg0m1_5 - 47/2028*ka1 + 71/2028*psi1 + 71/2028*psi2 
            - 37/2028*psi3 + 71/2028*psi4 + 47/2028*psi5, 7/4394*Dg0m1_2*psi3 
            + 35/4394*Dg0m1_2_4*psi1 + 33/4394*Dg0m1_2_5*psi1 - 11/2197*Dg0m1_3*psi2 
            - 35/4394*Dg0m1_3_4*psi1 - 15/2197*Dg0m1_3_5*psi1 - 15/2197*Dg0m1_4*psi2 
            - 11/2197*Dg0m1_4_5*psi1 - 35/4394*Dg0m1_5*psi2 - 10/2197*psi1^2 - 10/2197*psi2^2 
            + 33/4394*psi3^2 + 10/2197*psi4^2 + 15/2197*psi5^2 + 15/2197*ka2]

            sage: W = QSingularity.create('c33') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[3],A[3]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.chern_chars(0)
            0

            
        """        
        #coefficents of total chern character for kth line bundle
        ch = [] 
        n = self.n   #marked pts
        g = self.genus  #genus
        a = self.corrvec   #the correlator 
        A = self.FJRW      # the FJRW ring
        dim = self.dim()    #Dimension of Mgn
        R = self._Class_Poly_Ring()
        N = self.N         # number of variables
        
        if A.line_bundle_degrees(a)[k] == -1 and shortcut == True:
            ch = [0]
            #print "line bundle", k, ": degree = -1"
        else:
            r = A.singularity.matrix.det()  #big denominator for model see Chiodo paper  
            s = r*A.singularity.q[k]  #numerator for kth weight, if r is denom
            J = A[1].sector
            totalpoly = 0
            #numerators of kth coordinate of group elements:
            mbar = [r*a[j].sector[k] for j in range(n)]
            # mbar = []  
            # for j in range(n):
            #     mbar.append(r*a[j].sector[k])
            #sum from 0 to Dim    
            qk = (J)[k]
            ka0 = 2*g - 2 + n
            for i in range(dim + 1):
                totalpoly = 0
                psipoly = 0
                bdrypoly = 0
            
                #psi part of the sum:
                for j in range(0, n):
                    thetaj = a[j].sector
                    thetajk = (thetaj)[k]
                    psipoly -= bernoulli_polynomial(thetajk, i + 1)/(factorial(i + 1))*eval("psi" + str(j + 1))**i
                #print psipoly
                totalpoly += psipoly
            
                ##kappa part of the sum:
                totalpoly += bernoulli_polynomial(qk, i + 1)/(factorial(i + 1))*eval("ka" + str(i))
                #print bernoulli_polynomial(qk, i + 1)/(factorial(i + 1))*eval("ka" + str(i))
                
                #boundary part of the sum:
                if i > 0 :
                    #WARNING:  This will not handle n = 0, but is shouldn't have to, right?
                    b = self.divisors_by_genus_marks()  #each possible degree 1 boundary, or "cuts"
                    #sum over possible "cuts"
                    for bi in range(len(b)):
                        marks1 = b[bi][1]  #{ + } side marks
                        g1 = b[bi][0]   #{ + } side genus
                        g2 = g  - g1  # {-} side genus
                        n1 = len(marks1) + 1  #add one for { + } half edge
                        n2 = n - len(marks1) + 1   # add one for {-} half edge 
                        compmarks = [c + 1 for c in range(n)]
                        for item in marks1:
                            compmarks.remove(item)
                        marks2 = compmarks   # {-} side marks
                        #find group elements for each side
                        gp = (A[1].sector)*(2*g1 - 2 + n1)  #{ + } side group element
                        for item in marks1:
                            gp -= a[item - 1].sector
                        #gm = A[1].g*(2*g2 - 2 + n2)   #{-} side group element
                        #for item in marks2:
                        #    gm -= a[item - 1].g
                        gp = -gp
                        if i == 1: # for d = 1, the pushforward of 1 is just the degree 1 boundaries
                            # convert boundary to string for Drew's code.
                            # use markstring instead?
                            marklist = str(marks1[0])
                            for j in range(1, len(marks1)):
                                marklist += "_" + str(marks1[j])
                            delta = eval("Dg" + str(g1) + "m" + marklist)
                            # add this bdry's piece of the polynomial
                            bdrypoly = bernoulli_polynomial((gp[k]), i + 1)/(factorial(i + 1))*delta
                            #print i, bdrypoly
                            totalpoly += bdrypoly
                        
                        if i > 1:
                            """FIX THIS!!"""
                            
                            cut = marks1
                            psip = self.psiplus(cut)
                            psim = self.psiminus(cut)
                            #print cut, psip, psim
                        
                            #Make a string representation of K, for drew's code.
                            K = cut
                            strK = "Dg0m" + str(K[0])
                            for j in range(1, len(K)):
                                strK += "_" + str(K[j])
                            if psim =='0' and psip == '0':  
                                string1 = '0'
                                bdrypoly = 0
                                print("both = 0:", bdrypoly)
                            elif psim == '0':
                                string1 = strK + "*(-(" + psip + "))**" + str(i - 1)
                                #string1 = "(-(" + psip + "))**" + str(i - 1)
                                monom = eval(strK)*(-1*eval(psip))**(i - 1)
                                bdrypoly = bernoulli_polynomial(gp[k], i + 1)/(factorial(i + 1))*monom                       
                            elif psip =='0':
                                string1 = strK + "*(" + psim + ")**" + str(i - 1)
                                #string1 = "(" + psim + ")**" + str(i - 1)
                                monom = eval(strK)*(eval(psim))**(i - 1)
                                bdrypoly = bernoulli_polynomial(gp[k], i + 1)/(factorial(i + 1))*eval(string1)                       
                            else:
                                string1 = strK + "*((" + psim + ")**" + str(i - 1) #exp: i = 0, j = d - 1
                                #string1 = "((" + psim + ")**" + str(i - 1) #exp: i = 0, j = d - 1
                                for j in range(1, i):
                                    string1 += " + (-(" + psip + "))**" + str(j) + "*(" + psim + ")**" + str(i - j - 1)
                                string1 += ")"
                                bdrypoly = bernoulli_polynomial((gp[k]), i + 1)/(factorial(i + 1))*eval(string1)
                            #print i, "bdry", bdrypoly
                            totalpoly += bdrypoly
                    #print "TOTAL", i, totalpoly
                ch.append(totalpoly)
        #print "chern characters", k, ch
        return ch
    

    def chern_classes(self, k, shortcut = True):
        r"""
        Convert the chern character for -R1pi_* of  kth Line Bundle 
        to chern class of R1pi_*L_k up to degree D
        Using:
        
        .. math::   c_t(E) = \exp \left(\sum_{i = 1}^\infty \frac{(-1)^{(i-1)} ch_i(E)}{(i-1)!}
                                    \right)
        and 
        
        .. math::       c_t(E) = \frac{1}{c_t(-E)} = \frac{1}{1 + c_1(-E) + c_2(-E)+ \ldots}
        
        .. math::               = \frac{1}{1-(-c_1(-E) - c_2(-E) - \ldots)}
        
        .. math::               = \sum_{i=0}^\infty (-c_1(-E)-c_2(-E) - \ldots)^i
                        
        INPUT:
    
        - ``k`` -- an integer: the index of the Line Bundle
        - ``shortcut``-- if True uses rank of vector bundle 
                         to reduce number of necessary computations

        OUTPUT: 
        
        - ``chernclasses`` -- chern class coefficients: a list of polynomials in the 
            relevant kappa, psi, and boundary classes
            
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.chern_classes(0)
            [1, -71/2028*psi1 - 71/2028*psi2 + 37/2028*psi3 -
            71/2028*psi4 - 47/2028*psi5 + 47/2028*ka1 +
            83/2028*Dg0m1_2 - 97/2028*Dg0m1_3 + 47/2028*Dg0m1_4 +
            11/2028*Dg0m1_5 - 1/12*Dg0m1_2_3 + 11/2028*Dg0m1_2_4 -
            37/2028*Dg0m1_2_5 + 11/2028*Dg0m1_3_4 + 47/2028*Dg0m1_3_5
            - 97/2028*Dg0m1_4_5, 0]

            sage: W = QSingularity.create('c33') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[3],A[3]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.chern_classes(0)
            [1]

        """    

        h = self.chern_chars(k, shortcut = shortcut)  
        N = self.N
        D = self.RRD()
        linebundledegree = self.FJRW.line_bundle_degrees(self.corrvec, self.genus)[k]
        rank = self.genus - linebundledegree - 1    #Rank of pushforward bundle:
        ##shortcut means you don't have to go all the way up to D
        MaxDeg = min(rank, D, self.dim()) if shortcut else D
        if MaxDeg == 0 or h == [0]:
            return [1]               
        else:
        ##Create a polynomial ring with cohomology classes as variables
            R = self._Class_Poly_Ring()  
            S = PowerSeriesRing(R,'t',default_prec = MaxDeg+1)
            t, = S.gens()

            ##Adjusted chern character:  necessary to convert to chern class
            adjsum = t*S([((-1)**(i))*factorial(i)*h[i+1] for i in range(MaxDeg)]) 
            ##exponentiate
            TotalChClass1 = (adjsum.exp(MaxDeg+1)).truncate(MaxDeg+1)  #This is c_t(-R^1pi_*L)
            denom2 = (1 - TotalChClass1)
        ##totalchclass2 = 1/(totalchclass1) = 1/(1 - denom2) = 1 - denom2 + (denom2)^2 ...
        ##
            totalchclass2 = 1 + sum([((denom2).truncate(1+ceil((MaxDeg)/i))**i).truncate(MaxDeg+1) 
                                     for i in range(1,MaxDeg + 1)])
            
            if totalchclass2 != 1: #no coeffs of an integer (1), so have to treat separately.
                chernclasses = totalchclass2.list()+[0]*(D-totalchclass2.degree())
            else:
                chernclasses = [1]+[0]*D
            return chernclasses
                
    
    def Dth_chern_class_total(self, shortcut = True):
        '''
        Use chern classes of each line bundle to return (-1)^Dc_D(\\bigoplus R1pi_* L_i).
        Uses the relation
        .. math::   c_t(\\bigoplus E_i) = \\sum_{i=0}^\\infty c_t(E_i)
                         
        INPUT:
    
        - ``shortcut``-- if True uses rank of vector bundle 
                         to reduce number of necessary computations

        OUTPUT: 
        
        - ``Dth_coeff`` -- Dth chern class of the total bundle
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.Dth_chern_class_total()
            5893/4112784*psi1^2 + 5893/2056392*psi1*psi2 +
            5893/4112784*psi2^2 + 985/2056392*psi1*psi3 +
            985/2056392*psi2*psi3 - 2627/4112784*psi3^2 +
            5893/2056392*psi1*psi4 + 5893/2056392*psi2*psi4 +
            985/2056392*psi3*psi4 + 5893/4112784*psi4^2 +
            2341/2056392*psi1*psi5 + 2341/2056392*psi2*psi5 +
            1465/2056392*psi3*psi5 + 2341/2056392*psi4*psi5 +
            517/4112784*psi5^2 - 2341/2056392*psi1*ka1 -
            2341/2056392*psi2*ka1 - 1465/2056392*psi3*ka1 -
            2341/2056392*psi4*ka1 - 517/2056392*psi5*ka1 +
            517/4112784*ka1^2 - 2131/2056392*psi1*Dg0m1_2 -
            2131/2056392*psi2*Dg0m1_2 - 3631/2056392*psi3*Dg0m1_2 -
            2131/2056392*psi4*Dg0m1_2 + 413/2056392*psi5*Dg0m1_2 -
            413/2056392*ka1*Dg0m1_2 - 3071/4112784*Dg0m1_2^2 +
            2357/2056392*psi1*Dg0m1_3 + 2357/2056392*psi2*Dg0m1_3 +
            4313/2056392*psi3*Dg0m1_3 + 2357/2056392*psi4*Dg0m1_3 -
            571/2056392*psi5*Dg0m1_3 + 571/2056392*ka1*Dg0m1_3 +
            3745/2056392*Dg0m1_2*Dg0m1_3 - 4559/4112784*Dg0m1_3^2 -
            2341/2056392*psi1*Dg0m1_4 - 2341/2056392*psi2*Dg0m1_4 -
            1465/2056392*psi3*Dg0m1_4 - 2341/2056392*psi4*Dg0m1_4 -
            517/2056392*psi5*Dg0m1_4 + 517/2056392*ka1*Dg0m1_4 -
            413/2056392*Dg0m1_2*Dg0m1_4 + 571/2056392*Dg0m1_3*Dg0m1_4
            + 517/4112784*Dg0m1_4^2 + 2987/2056392*psi1*Dg0m1_5 +
            2987/2056392*psi2*Dg0m1_5 - 2185/2056392*psi3*Dg0m1_5 +
            2987/2056392*psi4*Dg0m1_5 + 2219/2056392*psi5*Dg0m1_5 -
            2219/2056392*ka1*Dg0m1_5 - 4229/2056392*Dg0m1_2*Dg0m1_5 +
            4963/2056392*Dg0m1_3*Dg0m1_5 -
            2219/2056392*Dg0m1_4*Dg0m1_5 - 1067/4112784*Dg0m1_5^2 +
            77/12168*psi1*Dg0m1_2_3 + 77/12168*psi2*Dg0m1_2_3 +
            17/12168*psi3*Dg0m1_2_3 + 77/12168*psi4*Dg0m1_2_3 +
            29/12168*psi5*Dg0m1_2_3 - 29/12168*ka1*Dg0m1_2_3 -
            23/12168*Dg0m1_2*Dg0m1_2_3 + 25/12168*Dg0m1_3*Dg0m1_2_3 -
            29/12168*Dg0m1_4*Dg0m1_2_3 + 43/12168*Dg0m1_5*Dg0m1_2_3 +
            1/144*Dg0m1_2_3^2 + 2987/2056392*psi1*Dg0m1_2_4 +
            2987/2056392*psi2*Dg0m1_2_4 - 2185/2056392*psi3*Dg0m1_2_4
            + 2987/2056392*psi4*Dg0m1_2_4 +
            2219/2056392*psi5*Dg0m1_2_4 - 2219/2056392*ka1*Dg0m1_2_4 -
            4229/2056392*Dg0m1_2*Dg0m1_2_4 +
            4963/2056392*Dg0m1_3*Dg0m1_2_4 -
            2219/2056392*Dg0m1_4*Dg0m1_2_4 -
            1067/2056392*Dg0m1_5*Dg0m1_2_4 +
            43/12168*Dg0m1_2_3*Dg0m1_2_4 - 1067/4112784*Dg0m1_2_4^2 -
            985/2056392*psi1*Dg0m1_2_5 - 985/2056392*psi2*Dg0m1_2_5 +
            2627/2056392*psi3*Dg0m1_2_5 - 985/2056392*psi4*Dg0m1_2_5 -
            1465/2056392*psi5*Dg0m1_2_5 + 1465/2056392*ka1*Dg0m1_2_5 +
            3631/2056392*Dg0m1_2*Dg0m1_2_5 -
            4313/2056392*Dg0m1_3*Dg0m1_2_5 +
            1465/2056392*Dg0m1_4*Dg0m1_2_5 +
            2185/2056392*Dg0m1_5*Dg0m1_2_5 -
            17/12168*Dg0m1_2_3*Dg0m1_2_5 +
            2185/2056392*Dg0m1_2_4*Dg0m1_2_5 -
            2627/4112784*Dg0m1_2_5^2 + 2987/2056392*psi1*Dg0m1_3_4 +
            2987/2056392*psi2*Dg0m1_3_4 - 2185/2056392*psi3*Dg0m1_3_4
            + 2987/2056392*psi4*Dg0m1_3_4 +
            2219/2056392*psi5*Dg0m1_3_4 - 2219/2056392*ka1*Dg0m1_3_4 -
            4229/2056392*Dg0m1_2*Dg0m1_3_4 +
            4963/2056392*Dg0m1_3*Dg0m1_3_4 -
            2219/2056392*Dg0m1_4*Dg0m1_3_4 -
            1067/2056392*Dg0m1_5*Dg0m1_3_4 +
            43/12168*Dg0m1_2_3*Dg0m1_3_4 -
            1067/2056392*Dg0m1_2_4*Dg0m1_3_4 +
            2185/2056392*Dg0m1_2_5*Dg0m1_3_4 -
            1067/4112784*Dg0m1_3_4^2 - 2341/2056392*psi1*Dg0m1_3_5 -
            2341/2056392*psi2*Dg0m1_3_5 - 1465/2056392*psi3*Dg0m1_3_5
            - 2341/2056392*psi4*Dg0m1_3_5 - 517/2056392*psi5*Dg0m1_3_5
            + 517/2056392*ka1*Dg0m1_3_5 -
            413/2056392*Dg0m1_2*Dg0m1_3_5 +
            571/2056392*Dg0m1_3*Dg0m1_3_5 +
            517/2056392*Dg0m1_4*Dg0m1_3_5 -
            2219/2056392*Dg0m1_5*Dg0m1_3_5 -
            29/12168*Dg0m1_2_3*Dg0m1_3_5 -
            2219/2056392*Dg0m1_2_4*Dg0m1_3_5 +
            1465/2056392*Dg0m1_2_5*Dg0m1_3_5 -
            2219/2056392*Dg0m1_3_4*Dg0m1_3_5 + 517/4112784*Dg0m1_3_5^2
            + 2357/2056392*psi1*Dg0m1_4_5 +
            2357/2056392*psi2*Dg0m1_4_5 + 4313/2056392*psi3*Dg0m1_4_5
            + 2357/2056392*psi4*Dg0m1_4_5 - 571/2056392*psi5*Dg0m1_4_5
            + 571/2056392*ka1*Dg0m1_4_5 +
            3745/2056392*Dg0m1_2*Dg0m1_4_5 -
            4559/2056392*Dg0m1_3*Dg0m1_4_5 +
            571/2056392*Dg0m1_4*Dg0m1_4_5 +
            4963/2056392*Dg0m1_5*Dg0m1_4_5 +
            25/12168*Dg0m1_2_3*Dg0m1_4_5 +
            4963/2056392*Dg0m1_2_4*Dg0m1_4_5 -
            4313/2056392*Dg0m1_2_5*Dg0m1_4_5 +
            4963/2056392*Dg0m1_3_4*Dg0m1_4_5 +
            571/2056392*Dg0m1_3_5*Dg0m1_4_5 - 4559/4112784*Dg0m1_4_5^2
                    
        '''
# TJ This next was supposed to be the right answer for the previous
# example, but it has the wrong dimension! D = 2, but he class has dim = 1.  
# The current answer above is what I have been getting for
# this, but I have no idea if it is actually right.  At least it has
# the right dimension.


#             -1/4112784*(37*Dg0m1_2 + 169*Dg0m1_2_3 + 97*Dg0m1_2_4 - 71*Dg0m1_2_5 - 47*Dg0m1_3
#             + 97*Dg0m1_3_4 - 11*Dg0m1_3_5 - 11*Dg0m1_4 - 47*Dg0m1_4_5 + 97*Dg0m1_5 - 11*ka1 + 
#             83*psi1 + 83*psi2 + 71*psi3 + 83*psi4 + 11*psi5)*(83*Dg0m1_2 - 169*Dg0m1_2_3 + 
#             11*Dg0m1_2_4 - 37*Dg0m1_2_5 - 97*Dg0m1_3 + 11*Dg0m1_3_4 + 47*Dg0m1_3_5 + 47*Dg0m1_4 
#             - 97*Dg0m1_4_5 + 11*Dg0m1_5 + 47*ka1 - 71*psi1 - 71*psi2 + 37*psi3 - 71*psi4 - 47*psi5)



        D = self.RRD()
        if D > self.dim():
            return 0
        elif D == 0:
            return 1
        else:
            R = self._Class_Poly_Ring()  
            S = PolynomialRing(R,'t')
            t, = S.gens()
            N = self.N       
       ##Form list of chern polynomials
            chern_polys =[S(self.chern_classes(i, shortcut = shortcut)).truncate(D+1) for i in range(N)]
       ## multiply them together and take the degree-D part
            total_ch_poly = prod(chern_polys)
            return (total_ch_poly.list()[-1])*(-1)**D



    def correlator(self, verbose=False, shortcut = True):
        """
        Compute the intersection number of (-1)^D c_D(\bigoplus R1 pi_* L_i)
        
        INPUT:
            
        - ``verbose`` 
        - ``shortcut``-- if True uses rank of vector bundle 
                         to reduce number of necessary computations
                         
        OUTPUT:
        
        -``number`` -- the value of the correlator
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.correlator()
            6/169

        
        """
        return self.intersect(self.Dth_chern_class_total(shortcut = shortcut))


        
    def intersect(self, poly, confirm = False):
        """
        Compute intersection number for the given polynomial
        
        INPUT:
            
        - ``poly``-- a polynomial in psi, kappa, delta classes
                         
        OUTPUT:
        
        -``number`` -- the intersection number of the polynomial ``poly``
        
        EXAMPLES::
    
            sage: from LGModels import * 
            sage: W = QSingularity.create('l223') 
            sage: G = SymmetryGroup(W,'J')
            sage: A = FJRWRing(G,print_basis=False)
            sage: a = [A[2], A[2],A[7],A[11],A[12]]
            sage: Mbar = ModuliSpace(A,a)
            sage: Mbar.intersect('psi1**2')
            1

        
        """
        # # Create a string version of the Dth Chern class
        # polystring = str(self.Dth_chern_class_total(shortcut = shortcut))
        
        def poly_iter(P): #convert poly P to an iterable of monomials as strings
            return iter(str(P).split(' + '))
        monomial_list = poly_iter(poly)
        names = self.class_list()
        reset(names)


        #recreate classes in Drew's setup
        M = self.drewspace()
        
        #make a dictionary to send class_list to classes
        x = self.class_list()
        x_vars = [eval(i) for i in x]
        ld = dict(zip(x,x_vars))
    
        ##Convert Dth_coeff back to classes and 
        ##calculate the intersection number
        return sum([intnum(sage_eval(pst, locals = ld), confirm = confirm) for pst in monomial_list])

            
    
    def split_vertex(self, G, v):
        """
        Return a list of "split" boundary graphs
        
        INPUT:
            
        - ``G`` -- a Graph
        - ``v`` -- a vertex in G
        
        OUTPUT:
        
        -``splitlist`` -- a list of stable graphs coming from G found by splitting vertex `v`
        
        """
        splitlist = []
        nblist = []
        alreadydone = []
        
        #remove v from all edges  !!!Where should edge label go?
        for e in G.edges():
            if v in [e[0], e[1]]:
                el = list(e)
                el.remove(v)
                
                #remove edge label piece corresponding to v
                vgpelem = e[2][v]
                s = list(e[2].items())
                s.remove((v, e[2][v]))
                newe2 = dict(s)
                #Add other vertex ( + edge label info) to v's neighbor list
                nblist.append([el[0], vgpelem, newe2])
        for subnb1 in subsets(nblist):
            if subnb1 not in alreadydone:
                compset = []
                for item in nblist:
                    if item not in subnb1:
                        compset.append(item)
                alreadydone.append(compset)
                n1 = len(subnb1)
                n2 = len(nblist) - n1
                for marks1 in subsets(v.marks):
                    m1 = len(marks1)
                    m2 = len(v.marks) - m1
                    for g1 in range(0, v.genus + 1):
                        g2 = v.genus - g1
                        #test to see if n1, m1, and g1 will create 2 stable nodes:
                        if 2*g1 - 2 + n1 + m1 + 1 > 0 and 2*g2 - 2 + n2 + m2 + 1 > 0:
                            #print "--- new split ---"
                            newedges = list(G.edges())
                            adjedges = [e for e in newedges if v in [e[0], e[1]]]
                            for e in adjedges:
                                newedges.remove(e)
                            #number of vertices    
                            vnum = len(G.vertices())
                        
                            #nbs = list of dictionaries giving edge information
                            nbs = []
                            for i in range(vnum + 1):
                                nbs.append({})
                            #for edges not adjacent to v:
                            #add edge info for e[0] and e[1], w/label e[2]
                            for e in newedges:
                                nbs[e[0].index][e[1]] = e[2]
    
                            
                            #first new node:
                            newv1 = vert(v.index, g1, marks1)
                            #print "newv1", newv1
                            marks2 = [m for m in v.marks if m not in marks1]
                            #second new node
                            newv2 = vert(vnum, g2, marks2)
                        
                            subnb2f = [item for item in nblist]
                            #subnb2f  = frozenset(nblist)
                            subnb2 = list(subnb2f)
                            for nv in subnb1:
                                subnb2.remove(nv)
                                s = nv[2].items()
                                s = dict(s)
                                s[newv1] = nv[1]
                                #newv1.index = v.index
                                if v.index < nv[0].index:
                                    nbs[v.index][nv[0]] = s
                                else:
                                    nbs[nv[0].index][newv1] = s
                            for nv in subnb2:
                                s = nv[2].items()
                                s = dict(s)
                                s[newv2] = nv[1]
                                nbs[nv[0].index][newv2] = s
                            gp1 = self.FJRW[1].sector
                            for mark in newv1.marks:
                                gp1 -= self.corrvec[mark - 1].sector
                                #print mark, self.corrvec[mark - 1].g
                                #print gp1
                            #print gp1
                            some_newv1_edges = nbs[newv1.index]
                            for item in some_newv1_edges:
                                gp1 -= some_newv1_edges[item][newv1]
                            for i in range(len(nbs)):
                                try:
                                    d = nbs[i][newv1]
                                    gp1 -= d[newv1]
                                except:
                                    pass
                            nbs[newv1.index][newv2] = {newv1:gp1, newv2:-gp1}
                        
                            #for nv in G.vertices():
                            #    if nv not in subnb1 and nv not in subnb2:
                            #        oldnb = [ov for ov in G.neighbors(nv) if nv.index < ov.index]
                            #        nbs[nv.index].append(oldnb)
                        
                            #New vertex set
                            newvertices = list(G.vertices())
                            newvertices.remove(v)
                            newvertices.insert(v.index, newv1)
                            newvertices.append(newv2)
                            newvertices.sort(key = lambda x:x.index)
                        
                            newdict = dict(zip(newvertices, nbs))
                            Gnew = Graph(newdict)
                            splitlist.append(Gnew)
        return splitlist

        
    def next_split(self, thislist):
        """
        Take a list of degree d - 1 graphs, return a list of degree d graphs, 
        a corresponding set of degonestrings, and a list of degree one graphs.
        
        INPUT:
        
        -``thislist`` -- 
        
        OUTPUT:
        - a list of three lists:
            - ``nextdeglist`` -- a list of degree d graphs
            - ``bdryonestr`` -- a list of lists of boundary one graph strings
            - ``usefulstuff`` -- a list of lists of boundary one graphs
        
        """
        nextdeglist = []
        bdryonestr = []
        extralist = []
        camefrom = []
        usefulstuff = []
        for bdry in thislist:
            #print "split", bdry, bdry.vertices()
            for v in bdry.vertices():
                splits = self.split_vertex(bdry, v)
                if len(splits) > 0:
                    for G in splits:
                        strG = self.graph_dict(G)
                        collapse = self.collapse_graph(strG)
                        degones = collapse[0]
                        if set(degones) not in extralist:
                            bdryonestr.append(degones)
                            extralist.append(set(degones))
                            nextdeglist.append(G)
                            camefrom.append([bdry, v])
                            usefulstuff.append(collapse[1])
        return [nextdeglist, bdryonestr, usefulstuff]
    
    

      
    def all_deg_bdry_graphs(self):
        """
        Return a list of all boundary graphs, each item is made up of vertex information
        For a given vertex, return marks and edge group elements
        
        """
        #Find a list of degree one boundary graphs        
        vec = self.divisors_by_genus_marks()
        G1 = []
        #Create a graph object with desired vertices and edges
        for item in vec:
            #items 0 and 2 are genera
            #items 1 and 3 are marks
            v1 = vert(0, item[0], item[1])
            v2 = vert(1, item[2], item[3])
            #Find group element attached to v1 side of edge
            g1 = self.FJRW[1].sector *(len(item[1]) - 1)
            for mark in item[1]:
                g1 -= self.corrvec[mark - 1].sector
            # create graph object.  
            #edge labeled w dictionary mapping vertices to relevant gp elements
            bd = Graph({v1:{v2:{v1:g1, v2:-g1}}})
            G1.append(bd)     
        
        #Add string description of each bdry one graph"
        G1p = []
        for G in G1:
            G1p.append(self.deg_one_string(G))
        currentlist = [G1, G1p]

        l = len(G1)
        allgraphs = []
        #Find all higher degree stable graphs
        while l > 0:
            allgraphs.append(currentlist)
            #split currentlist graphs into graphs with one more edge
            currentlist = self.next_split(currentlist[0])
            l = len(currentlist[0])
        biglist = []
        for i in range(len(allgraphs)):
            # for a given graph, we want to remember all node information:
            for G in allgraphs[i][0]:
                thisgraph = []
                # for a given node, we want to know the marks, and edge groups elements:
                for v in G.vertices():
                    gps = []
                    for e in G.edges():
                        try:    
                            gp = e[2][v]
                            gps.append(gp)
                        except:
                            pass
                    thisgraph.append([list(v.marks), gps])
                biglist.append(thisgraph)
        return biglist
        
    def graph_dict(self, G):
        """ 
        Return a dictionary to use for defining G 
        
        INPUT:
        
        - ``G``-- a Graph
        
        OUTPUT:
        
        - ``defineG`` -- string representation of a dictionary which can be used to define G
        
        """
        nblist = []    
        for nv in G.vertices():
            nbs = [ov for ov in G.neighbors(nv) if nv.index < ov.index]
            nblist.append(nbs)
        defineG = dict(zip(G.vertices(), nblist))
        defineG = str(defineG)
        return defineG            
    
        
    def collapse_graph(self, strG):
        """
        Return a list of degree one graphs that are all collapses of G
        
        INPUT:
        
        -``strG`` -- a string which can be used to define a graph G
        
        OUTPUT:
        
        - a list of two lists
            - ``degonelist`` -- a list of degree one graph strings
            - ``degonegraphs`` -- a list of degree one graphs
        
        """
        
        degonelist = []
        degonegraphs = []
        G = Graph(eval(strG))
        for e in G.edges(labels=False):
            G = Graph(eval(strG))
            edges = list(G.edges(labels=False))
            if e in edges:
                edges.remove(e)
            else:
                edges.remove((e[1], e[0]))
            while len(edges) > 0:
                ed = edges[0]
                edges.remove(ed)
                if ed[0].index < ed[1].index:
                    v1 = ed[0]
                    v2 = ed[1]
                else:
                    v1 = ed[1]
                    v2 = ed[0]
                n1 = v1.index
                n2 = v2.index
                v3 = vert(n1 + .5, v1.genus + v2.genus, v1.marks.union(v2.marks))
                G.delete_edge((v1, v2))
                G.add_vertex(v3)
                for edg in G.edges(labels=False):
                    bool1 = v1 ==edg[0] and v1 == edg[1]
                    bool2 = v1 == edg[0] and v2 == edg[1]
                    bool3 = v2 == edg[0] and v1 == edg[1]
                    bool4 = v2 == edg[0] and v2 == edg[1]
                    if bool1 or bool2 or bool3 or bool4:
                        print("Problem!")
                        ### This is for loops, might not work yet.
                        #edg = (v3, v3)
                    else:
                        if v1 == edg[0] or v2 == edg[0]:
                            G.add_edge(edg[1], v3)                            
                            G.delete_edge(edg)
                            if edg in edges:
                                edges.remove(edg)
                                edges.append((edg[1], v3))
                            elif (edg[1], edg[0]) in edges:
                                edges.remove((edg[1], edg[0]))
                                edges.append((edg[1], v3))
                            
                        if v1 == edg[1] or v2 == edg[1]:
                            G.add_edge(edg[0], v3)
                            G.delete_edge(edg)
                            if edg in edges:
                                edges.remove(edg)
                                edges.append((edg[0], v3))
                            elif (edg[1], edg[0]) in edges:
                                edges.remove((edg[1], edg[0]))
                                edges.append((edg[0], v3))
                    
                G.delete_vertex(v1)
                G.delete_vertex(v2)
                v3.index -= .5
            degoneG = self.deg_one_string(G)
            degonelist.append(degoneG)
            degonegraphs.append(G)
        return [degonelist, degonegraphs]
    
    def deg_one_string(self, G):
        """
        Return a string name for G that will work in Drew's code
        
        ..WARNING::
            This won't work for graphs which are not degree one, or which have no marks.
        
        """
        st = "Dg"
        v=G.vertices()
        for v in G.vertices():
            if 1 in v.marks:
                marks = list(v.marks)
                marks.sort()
                markstring = str(marks[0])
                for i in range(1, len(marks)):
                    markstring += "_" + str(marks[i])
                st += str(v.genus) + "m" + markstring
        return st
        
        
class vert:
    """
    Class that stores information about a vertex
    
    CONSTRUCTOR:
    - ``genus``
    - ``marks`` -- should be a set
    - ``neighbors`` -- adjacent edges
    
    .. TODO:
        Add Error for 2*g - 2 + n <= -
        
    """
    def __init__(self, index, genus, marks):
        """Constructor: see class documentation"""
        self.genus = genus
        marks = list(marks)
        marks.sort()
        self.marks = set(marks)
        self.index = index
        
    def __str__(self):
        return "vert(" + str(self.index) + ", " + str(self.genus) + ", " + str(self.marks) + ")"
    
    def __repr__(self):
        return str(self)
    
    def __hash__(self):
        return hash(1)

    def __lt__(self,other):
        return str(self.marks)<str(other.marks)

    
    def __eq__(self, compare):
        equal = False
        if self.genus == compare.genus and self.marks ==compare.marks:
            if self.index == compare.index:
                equal = True
        return equal
        
########################################
# The following methods might be       #
# useful for optimizing the            #
# ModuliSpace.all_boundary_concave()   #
# method in case it gets really slow   #
# creating the same genus-g, n-pointed #
# graphs in lots of different problems #
########################################


    """    
    def deg_one_gen(self):
        List of degree one boundary graphs
        vec = self.divisors_by_genus_marks()
        degonegraphlist = []
        #Create a graph object with desicred vertices and edges
        for item in vec:
            #items 0 and 2 are genera
            #items 1 and 3 are marks
            v1 = vert(0, item[0], item[1])
            v2 = vert(1, item[2], item[3])
            #Find polynomial for group element attached to v1 side of edge
            var('J')
            gplus = J *(len(item[1]) - 1)
            for mark in item[1]:
                g = "gp" + str(mark)
                g = var(g)
                gplus += -g
            # create graph object.  
            #edge labeled w dictionary mapping vertices to relevant gp elements
            bd = Graph({v1:{v2:{v1:gplus, v2:-gplus}}})
            degonegraphlist.append(bd)
        return degonegraphlist
    """
   
   
    """
    def split_vertex_gen(self, G, v):
        
        Check that edges match
        Should return a list of "split" boundary graphs
        
        
        splitlist = []
        
        #v's neighbor nodes:
        nblist = []
        
        alreadydone = []
        
        #remove v from all edges  !!!Where should edge label go?
        for e in G.edges():
            if v in [e[0], e[1]]:
                el = list(e)
                el.remove(v)
                
                #remove edge label piece corresponding to v
                vgpelem = e[2][v]
                s = e[2].items()
                s.remove((v, e[2][v]))
                newe2 = dict(s)
                
                #Add other vertex ( + edge label info) to v's neighbor list
                nblist.append([el[0], vgpelem, newe2])

        for subnb1 in subsets(nblist):
            if subnb1 not in alreadydone:
                compset = []
                for item in nblist:
                    if item not in subnb1:
                        compset.append(item)
                alreadydone.append(compset)
                n1 = len(subnb1)
                n2 = len(nblist) - n1
                for marks1 in subsets(v.marks):
                    m1 = len(marks1)
                    m2 = len(v.marks) - m1
                    for g1 in range(0, v.genus + 1):
                        g2 = v.genus - g1
                        #test to see if n1, m1, and g1 will create 2 stable nodes:
                        if 2*g1 - 2 + n1 + m1 + 1 > 0 and 2*g2 - 2 + n2 + m2 + 1 > 0:
                            #print "--- new split ---"
                            newedges = G.edges()
                            adjedges = [e for e in newedges if v in [e[0], e[1]]]
                            for e in adjedges:
                                newedges.remove(e)
                            #number of vertices    
                            vnum = len(G.vertices())
                        
                            #nbs = list of dictionaries giving edge information
                            nbs = []
                            for i in range(vnum + 1):
                                nbs.append({})
                            #for edges not adjacent to v:
                            #add edge info for e[0] and e[1], w/label e[2]
                            for e in newedges:
                                nbs[e[0].index][e[1]] = e[2]
    
                            
                            #first new node:
                            newv1 = vert(v.index, g1, marks1)
                            #find number of edges at this new vertex
                            countk = len(marks1)
                            countk += len(subnb1)
                            countk += 1
                            #print "newv1", newv1
                            marks2 = [m for m in v.marks if m not in marks1]
                            #second new node
                            newv2 = vert(vnum, g2, marks2)
                        
                            subnb2f = [item for item in nblist]
                            #subnb2f  = frozenset(nblist)
                            subnb2 = list(subnb2f)
                            for nv in subnb1:
                                subnb2.remove(nv)
                                s = nv[2].items()
                                s = dict(s)
                                s[newv1] = nv[1]
                                #newv1.index = v.index
                                if v.index < nv[0].index:
                                    nbs[v.index][nv[0]] = s
                                else:
                                    nbs[nv[0].index][newv1] = s
                            for nv in subnb2:
                                s = nv[2].items()
                                s = dict(s)
                                s[newv2] = nv[1]
                                nbs[nv[0].index][newv2] = s
                            gplus = (countk - 2)*J
                            for mark in newv1.marks:
                                gs = "gp" + str(mark)
                                gnew = eval(gs)
                                gplus -= gnew

                            #edges saved using newv1's index:
                            some_newv1_edges = nbs[newv1.index]
                            for item in some_newv1_edges:
                                gplus -= some_newv1_edges[item][newv1]
                                
                            #edges saved using other vertex' index:
                            for i in range(len(nbs)):
                                try:
                                    d = nbs[i][newv1]
                                    gplus -= (d[newv1])
                                except:
                                    pass
                            nbs[newv1.index][newv2] = {newv1:gplus, newv2:-gplus}
                        
                            #for nv in G.vertices():
                            #    if nv not in subnb1 and nv not in subnb2:
                            #        oldnb = [ov for ov in G.neighbors(nv) if nv.index < ov.index]
                            #        nbs[nv.index].append(oldnb)
                        
                            #New vertex set
                            newvertices = list(G.vertices())
                            newvertices.remove(v)
                            newvertices.insert(v.index, newv1)
                            newvertices.append(newv2)
                            newvertices.sort(key = lambda x:x.index)
                        
                            newdict = dict(zip(newvertices, nbs))
                            Gnew = Graph(newdict)
                            splitlist.append(Gnew)
        return splitlist
    """
    
    
    """
    def next_split_gen(self, thislist):
        
        This method works.  take a list of degree d - 1 graphs, 
        return a list of degree d graphs, a corresponding set of degonestrings, and 
        a list of degree one graphs.  
        
        
        nextdeglist = []
        bdryonestr = []
        extralist = []
        camefrom = []
        usefulstuff = []
        for bdry in thislist:
            #print "split", bdry, bdry.vertices()
            for v in bdry.vertices():
                splits = self.split_vertex_gen(bdry, v)
                if len(splits) > 0:
                    for G in splits:
                        strG = self.graph_dict(G)
                        collapse = self.collapse_graph(strG)
                        degones = collapse[0]
                        if set(degones) not in extralist:
                            bdryonestr.append(degones)
                            extralist.append(set(degones))
                            nextdeglist.append(G)
                            camefrom.append([bdry, v])
                            usefulstuff.append(collapse[1])
        return [nextdeglist, bdryonestr, usefulstuff]
    """
    """    
    def all_bdry_graphs_gen(self):
        
        Return a list of all boundary graphs, each item is made up of vertex information
        For a given vertex, return marks and edge group elements
        
        
        G1 = self.deg_one_gen()
        G1p = []
        l = len(G1)
        #print l
        allgraphs = []
        #Add more information for the bdry one things?"
        for G in G1:
            G1p.append(self.deg_one_string(G))
        currentlist = [G1, G1p]
        while l > 0:
            #print "currentlist length", l
            allgraphs.append(currentlist)
            currentlist = self.next_split_gen(currentlist[0])
            l = len(currentlist[0])
        biglist = []
        for i in range(len(allgraphs)):
            # for a given graph, we want to remember all node information:
            for G in allgraphs[i][0]:
                thisgraph = []
                # for a given node, we want to know the marks, and edge groups elements:
                for v in G.vertices():
                    gps = []
                    for e in G.edges():
                        try:    
                            gp = e[2][v]
                            gps.append(gp)
                        except:
                            pass
                        #print G.edges(labels=False)
                    print v, gps
                    thisgraph.append([list(v.marks), gps])
                biglist.append(thisgraph)
        #        allgraphs.append(thisgraph)
        return biglist
    """



##NOTE: to compute the D4 case, this is all you need:

# W = Qs("rc32")
# G = Grp(W,"J")
# A = Am(G)

# a = [A[4],A[4],A[4], A[4],A[4],A[4],A[4]] 
# g = 0

# Mbar = ModuliSpace(A,a,g)
# print Mbar.correlator()
