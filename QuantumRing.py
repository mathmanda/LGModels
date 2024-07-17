"""
This module contains:

    QuantumRingElement
        Data Attributes:
            is_narrow
            degree
            bi_degree
            sector
            index
            monomial
            parent_ring
            is_homogeneous
            is_bi_homogeneous
            in_basis

    QuantumRingBasisElement
        Data Attributes:
            is_narrow
            degree
            bi_degree
            sector
            index
            monomial
            parent_ring
            name
         
    QuantumRing
        Methods:
            mirror
            mirror_summary
            pair
            pairing_on_basis
            print_summary
            products
        Data Attributes:
            Gsec
            Ginv
            singularity
            basis_by_name
            eta
            eta_inv
            sectors
    
    CouldNotComputeException
    
You can use Sage to compute a QuantumRing, which has the structure of a
Frobenius Algebra over a finite basis determined by a quasihomogeneous
nondegenerate polynomial and group. The QuantumRing class and associated classes
are abstract base classes for the A and B models of Landau-Ginzburg mirror
symmetry. Code for the A model is found in FJRW.py and code for the B model is
found in OrbMilnor.py.

The following is a description of the internal structure of QuantumRing and its
associated classes. QuantumRing inherits from CombinatorialFreeModule (and sets
the category to algebra), and hence its elements are finite linear combinations
of some basis elements. The __init__ method of QuantumRing constructs this list
of basis elements in the QuantumRing._compute() method. These basis elements
must inherit from QuantumRingBasisElement. These basis elements cannot be added
or multiplied, but they do keep track of attributes such as monomial, sector,
degree, and an index corresponding to their order in the basis.

The element class for QuantumRing, which is QuantumRingElement, inherits from
CombinatorialFreeModuleElement. These are the objects the user sees in the
terminal window. The QuantumRingBasisElement objects are "wrapped" in this
element class, at which point Sage knows how to add and multiply them. So, 
for example, if I construct a QuantumRing `Q`, and then ask it for its first
basis element `Q[1]`, the object I get is a QuantumRingElement, not a 
QuantumRingBasisElement. The most direct way to access the underlying basis
elements is to use the method `Q[1].monomial_coefficients()`, which returns
a dictionary whose keys are QuantumRingBasisElement objects and whose values
are elements of the base ring.

The __mul__ method for QuantumRingElements is implemented by the category
structure (we set the category to algebra). However, that implementation
requires a method called product_on_basis be implemented by QuantumRing.
Since the A and B model products are different, this method is coded in the
FJRWRing and OrbMilnorRing classes. In imitation of this structure, the
method QuantumRing.pair() calls a pairing_on_basis method. Both of these are
implemented in QuantumRing since they are the same for the A and B models.
Both product_on_basis and pairing_on_basis take as arguments legitimate
basis elements of the ring - that is, instances of QuantumRingBasisElement.


AUTHORS:

    - Drew Johnson (2010-2011) Initial design and implementation
    - Scott Mancuso (2012) Refactoring and documentation
    - Rachel Suggs (Sep 2012) Refactoring to inherit from existing Sage objects

"""
# if not __name__ == '__main__':  # i.e. if this is being imported rather than
                                # read as a load or attach.
try:
    from sage.all import *
except ImportError:
    print("Didn't import Sage!!!")

import os
import sys
import atexit
import warnings
if "." not in sys.path: sys.path.insert(1,".")

from LazyAttr import lazy_attr

COHOMOLOGY_ROOT = os.getenv("COHOMOLOGY_ROOT", default=os.getcwd())
"""The directory that contains this computer's copy of the code."""
PRODUCTS_DICT_DIRECTORY = os.path.join(COHOMOLOGY_ROOT, ".products_db/")
"""The directory that contains the database of already computed products."""
PAIRINGS_DICT_DIRECTORY = os.path.join(COHOMOLOGY_ROOT, ".pairings_db/")
"""The directory that contains the database of already computed pairings."""

if not os.path.exists(PRODUCTS_DICT_DIRECTORY):
    os.mkdir(PRODUCTS_DICT_DIRECTORY)
if not os.path.exists(PAIRINGS_DICT_DIRECTORY):
    os.mkdir(PAIRINGS_DICT_DIRECTORY)



from sage.misc.cachefunc import cached_method
try:
     from sage.misc.interpreter import SageInteractiveShell as sis
except ImportError:
     from sage.repl.interpreter import SageTerminalInteractiveShell as sis
from sage.sets.family import Family
from sage.categories.all import GradedAlgebrasWithBasis
from sage.combinat.free_module import CombinatorialFreeModule, IndexedFreeModuleElement
from sage.categories.all import tensor

class QuantumRingElement(IndexedFreeModuleElement):
    """
    Abstract base class for :class:`~FJRW.FJRWRingElement` and
    :class:`~OrbMilnor.OrbMilnorRingElement`. These are the element classes
    for :class:`~FJRW.FJRWRing` and :class:`~OrbMilnor.OrbMilnorRing`,
    respectively. See those classes for further documentation.
    
    CONSTRUCTOR:
    
    - ``parent`` -- The :class:`~QuantumRing.QuantumRing` that this basis
      element lives in.
    - ``data`` -- A dictionary of :class:`~QuantumRing.QuantumRingBasisElement`
      and coefficients that describes this basis element (I think).
    
    .. NOTE::
    
        Users should not call the constructor directly. Instead they
        should create an instance of :class:`~FJRW.FJRWRing` or
        :class:`~OrbMilnor.OrbMilnorRing` which will populate a list of
        basis elements.
    
    """
    def __init__(self, parent, data):
        super(QuantumRingElement, self).__init__(parent, data)
    
    def factor(self):
        """
        Return a list of known factors of self.
        
        OUTPUT:
        
        - The attribute self._factors is a list of tuples. Each tuple contains a
          scalar and two :class:`~!QuantumRing.QuantumRingElement` s which,
          when multiplied, yield self.
        
        Note on implementation: This method returns the `_factors` attribute of
        the basis element corresponding to self, which is a list populated by
        self.parent.products(). If the user has not called
        self.parent.products() previous to calling this method, it is called by
        the method.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: G = SymmetryGroup(QSingularity.create("L23"), "max")
            sage: A = FJRWRing(G)
            FJRW ring for x^2*y + x*y^3 with group generated by <(1/5, 3/5)>.
            Dimension:   6
            Basis:
              [1]  e_(2/5, 1/5)  Degree: 0    (0, 0)
              [2]  e_(1/5, 3/5)  Degree: 2/5  (1/5, 1/5)
              [3]  y^2e_(0, 0)   Degree: 4/5  (2/5, 2/5)
              [4]  xe_(0, 0)     Degree: 4/5  (2/5, 2/5)
              [5]  e_(4/5, 2/5)  Degree: 6/5  (3/5, 3/5)
              [6]  e_(3/5, 4/5)  Degree: 8/5  (4/5, 4/5)    
              
            sage: A[6].factor()
            [(1, e_(2/5, 1/5), e_(3/5, 4/5)), (1, e_(1/5, 3/5), e_(4/5, 2/5)),
            (-5/2, y^2e_(0, 0), y^2e_(0, 0)), (5, y^2e_(0, 0), xe_(0, 0)),
            (-5/3, xe_(0, 0), xe_(0, 0))]
            sage: [prod(factors) for factors in A[6].factor()]
            [e_(3/5, 4/5), e_(3/5, 4/5), e_(3/5, 4/5), e_(3/5, 4/5), e_(3/5,
            4/5)]
            
            sage: G = SymmetryGroup(QSingularity.create("C49"),"J")
            sage: A = FJRWRing(G)
            FJRW ring for x^4*y + y^9 with group generated by <(1/9, 5/9)>.
            Dimension:   12
            Basis:
              [1]  e_(2/9, 1/9)     Degree: 0    (0, 0)
              [2]  e_(1/9, 5/9)     Degree: 2/3  (1/3, 1/3)
              [3]  e_(4/9, 2/9)     Degree: 2/3  (1/3, 1/3)
              [4]  y^6e_(0, 0)      Degree: 4/3  (2/3, 2/3)
              [5]  x*y^4e_(0, 0)    Degree: 4/3  (2/3, 2/3)
              [6]  x^2*y^2e_(0, 0)  Degree: 4/3  (2/3, 2/3)
              [7]  x^3e_(0, 0)      Degree: 4/3  (2/3, 2/3)
              [8]  e_(1/3, 2/3)     Degree: 4/3  (2/3, 2/3)
              [9]  e_(2/3, 1/3)     Degree: 4/3  (2/3, 2/3)
             [10]  e_(5/9, 7/9)     Degree: 2    (1, 1)
             [11]  e_(8/9, 4/9)     Degree: 2    (1, 1)
             [12]  e_(7/9, 8/9)     Degree: 8/3  (4/3, 4/3)
            
            sage: A[12].factor()
            Warning... computed the correlator <H[2], H[2], H[7]> up to a factor of -1
            [(1, e_(2/9, 1/9), e_(7/9, 8/9)), (1, e_(1/9, 5/9), e_(8/9, 4/9)),
            (1, e_(4/9, 2/9), e_(5/9, 7/9)), (36, y^6e_(0, 0), x^2*y^2e_(0, 0)),
            (36, x*y^4e_(0, 0), x*y^4e_(0, 0)), (-4, x^3e_(0, 0), x^3e_(0, 0)),
            (1, e_(1/3, 2/3), e_(2/3, 1/3))]
            sage: A[6].factor()
            [(1, e_(2/9, 1/9), x^2*y^2e_(0, 0))]

        
        Note that even primitive elements will have at least one pair of
        factors: the identity and self::
        
            sage: A[2].factor()
            [(1, e_(2/9, 1/9), e_(1/9, 5/9))]
        
        
        .. NOTE::
        
            Right now this is only implemented for basis elements.
        
        """
        if not self.in_basis:
            raise NotImplementedError("This method is only implemented for basis elements.")
        # If the user hasn't yet computed products, we will for them.
        elif not self.leading_support()._factors:
            self.parent().products(print_to_screen=False)
        # Whether or not we needed to call products, return the factors.
        return self.leading_support()._factors
    
    def __str__(self):
        """
        Return a string giving a simple, human-friendly version of ``self``.
        This string represents this basis element by its index in
        :attr:`~QuantumRing.BasisElement.myRing`'s :attr:`list of basis elements
        <QuantumRing.QuantumRing.basis>`.
        
        This is copied from free_module's _repr_ method, but instead of using _repr_term it uses _str_term.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: G = SymmetryGroup(QSingularity.create("L23"), "max")
            sage: A = FJRWRing(G)
            sage: l = A[6].factor()
            sage: p = l[0]
            sage: print p[2]
            H[6]
            
        """
        v = self._monomial_coefficients.items()
        try:
            v.sort()
        except: # Sorting the output is a plus, but if we can't, no big deal
            pass
        str_term = self.parent()._str_term
        v = [ (str_term(m),x) for (m, x) in v ]
        #if v:
        #    mons, cffs = zip(*v)
        #else:
        #    mons = cffs = []
        ast = self.parent()._print_options.get('scalar_mult', "*")
        x = repr_lincomb( v, scalar_mult=ast).replace("%s1 "%ast," ")
        if x[len(x)-2:] == "%s1"%ast:
            x = x[:len(x)-2]
        return x
    
    def __int__(self):
        return self.index
    
    @lazy_attr
    def is1(self):
        """
        Return True if this element is the one-element of the ring.
        
        .. NOTE::
        
            This method has been deprecated. Use `is_one` instead.
        
        """
        ###################################################
        warnings.warn("is1() has been deprecated and will be removed in a future version of TheCode. Use is_one() instead.", stacklevel = 3)
        ################################################### 
        return self.is_one()
        
    @lazy_attr
    def is_narrow(self):
        """
        Return ``True`` if this is a narrow element. An element is narrow if 
        it is a linear combination of basis elements with group elements 
        with trivial fixed loci.
        
        EXAMPLES:
        
            sage: from LGModels import *
            sage: W = Qs("F4C32").transpose()
            sage: G = Grp(W, [[3/4, 2/3, 2/3]])
            sage: A = Am(G)
            FJRW ring for x^4 + y^3 + y*z^2 with group generated by <(3/4, 2/3, 2/3)>.
            Dimension:   12
            Basis:
              [1]  e_(1/4, 1/3, 1/3)  Degree: 0     (0, 0)
              [2]  e_(1/2, 1/3, 1/3)  Degree: 1/2   (1/4, 1/4)
              [3]  ze_(1/4, 0, 0)     Degree: 2/3   (1/3, 1/3)
              [4]  ye_(1/4, 0, 0)     Degree: 2/3   (1/3, 1/3)
              [5]  e_(3/4, 1/3, 1/3)  Degree: 1     (1/2, 1/2)
              [6]  ze_(1/2, 0, 0)     Degree: 7/6   (7/12, 7/12)
              [7]  ye_(1/2, 0, 0)     Degree: 7/6   (7/12, 7/12)
              [8]  e_(1/4, 2/3, 2/3)  Degree: 4/3   (2/3, 2/3)
              [9]  ze_(3/4, 0, 0)     Degree: 5/3   (5/6, 5/6)
             [10]  ye_(3/4, 0, 0)     Degree: 5/3   (5/6, 5/6)
             [11]  e_(1/2, 2/3, 2/3)  Degree: 11/6  (11/12, 11/12)
             [12]  e_(3/4, 2/3, 2/3)  Degree: 7/3   (7/6, 7/6)
            sage: (A[2]+(3/2)*A[5]-A[8]).is_narrow
            True
            sage: (A[2]+A[4]).is_narrow
            False
            
            sage: W = QSingularity.create("C45F7")
            sage: G = SymmetryGroup(W, "max")
            sage: A = FJRWRing(G)
            FJRW ring for x^4*y + y^5 + z^7 with group generated by <(3/20, 2/5, 1/7)>.
            Dimension:   102
            Basis:
              [1]  e_(1/5, 1/5, 1/7)    Degree: 0       (0, 0)
              [2]  e_(1/5, 1/5, 2/7)    Degree: 2/7     (1/7, 1/7)
              [3]  e_(3/20, 2/5, 1/7)   Degree: 3/10    (3/20, 3/20)
              [4]  e_(9/20, 1/5, 1/7)   Degree: 1/2     (1/4, 1/4)
              [5]  e_(1/5, 1/5, 3/7)    Degree: 4/7     (2/7, 2/7)
              [6]  e_(3/20, 2/5, 2/7)   Degree: 41/70   (41/140, 41/140)
              [7]  e_(1/10, 3/5, 1/7)   Degree: 3/5     (3/10, 3/10)
              [8]  e_(9/20, 1/5, 2/7)   Degree: 11/14   (11/28, 11/28)
              [9]  e_(2/5, 2/5, 1/7)    Degree: 4/5     (2/5, 2/5)
             [10]  e_(1/5, 1/5, 4/7)    Degree: 6/7     (3/7, 3/7)
             [11]  e_(3/20, 2/5, 3/7)   Degree: 61/70   (61/140, 61/140)
             [12]  e_(1/10, 3/5, 2/7)   Degree: 31/35   (31/70, 31/70)
             [13]  e_(1/20, 4/5, 1/7)   Degree: 9/10    (9/20, 9/20)
             [14]  e_(7/10, 1/5, 1/7)   Degree: 1       (1/2, 1/2)
             [15]  e_(9/20, 1/5, 3/7)   Degree: 15/14   (15/28, 15/28)
             [16]  e_(2/5, 2/5, 2/7)    Degree: 38/35   (19/35, 19/35)
             [17]  e_(7/20, 3/5, 1/7)   Degree: 11/10   (11/20, 11/20)
             [18]  e_(1/5, 1/5, 5/7)    Degree: 8/7     (4/7, 4/7)
             [19]  e_(3/20, 2/5, 4/7)   Degree: 81/70   (81/140, 81/140)
             [20]  e_(1/10, 3/5, 3/7)   Degree: 41/35   (41/70, 41/70)
             [21]  e_(1/20, 4/5, 2/7)   Degree: 83/70   (83/140, 83/140)
             [22]  x^3e_(0, 0, 1/7)     Degree: 6/5     (3/5, 3/5)
             [23]  e_(7/10, 1/5, 2/7)   Degree: 9/7     (9/14, 9/14)
             [24]  e_(13/20, 2/5, 1/7)  Degree: 13/10   (13/20, 13/20)
             [25]  e_(9/20, 1/5, 4/7)   Degree: 19/14   (19/28, 19/28)
            ...
            sage: A[22].is_narrow
            False
            sage: A[23].is_narrow
            True
            sage: (A[22]+A[23]).is_narrow
            False
            sage: (A[23]+A[24]).is_narrow
            True
            
            sage: W = QSingularity.create("F6C32")
            sage: G = SymmetryGroup(W, [[1/3, 1/6, 1/2]])
            sage: B = OrbMilnorRing(G)
            Orbifold Milnor ring for x^6 + y^3*z + z^2 with group generated by <(2/3, 5/6, 1/2)>.
            Dimension:   8
            Basis:
              [1]  b_(0, 0, 0)         Degree: 0    (0, 0)
              [2]  x^3b_(0, 0, 0)      Degree: 1    (1/2, 1/2)
              [3]  b_(1/3, 1/6, 1/2)   Degree: 4/3  (1/6, 7/6)
              [4]  x^2*y^2b_(0, 0, 0)  Degree: 4/3  (2/3, 2/3)
              [5]  x^2b_(0, 1/2, 1/2)  Degree: 4/3  (2/3, 2/3)
              [6]  b_(2/3, 5/6, 1/2)   Degree: 4/3  (7/6, 1/6)
              [7]  x*y*zb_(0, 0, 0)    Degree: 5/3  (5/6, 5/6)
              [8]  x^4*y*zb_(0, 0, 0)  Degree: 8/3  (4/3, 4/3)
            sage: B[1].is_narrow
            False
            sage: B[3].is_narrow
            True
            sage: B[5].is_narrow
            False
        
        """
        narrow = True
        for elem in self.support():
            if not elem.is_narrow:
                narrow = False
        return narrow
    
    @lazy_attr
    def degree(self):
        """
        Return the degree of this
        :class:`~QuantumRing.QuantumRingElement`. 
        
        OUTPUT:
        
        - A rational number giving the degree of this
          :class:`~!QuantumRing.QuantumRingElement`. The degree is the
          maximum of the degrees of the basis elements appearing with nonzero
          coefficients in a linear combination describing self. A warning is
          printed if self is not homogeneous.

        .. NOTE::
        
            The degree is the sum of the bi-degrees. See pg 13 of [Kr]_.
          
        EXAMPLES:
        
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G)
            Orbifold Milnor ring for x^4 + y^3*z + z^2 with group generated by <(0, 1/2, 1/2)>.
            Dimension:   12
            Basis:
              [1]  b_(0, 0, 0)         Degree: 0     (0, 0)
              [2]  xb_(0, 0, 0)        Degree: 1/2   (1/4, 1/4)
              [3]  y^2b_(0, 0, 0)      Degree: 2/3   (1/3, 1/3)
              [4]  b_(0, 1/2, 1/2)     Degree: 2/3   (1/3, 1/3)
              [5]  x^2b_(0, 0, 0)      Degree: 1     (1/2, 1/2)
              [6]  x*y^2b_(0, 0, 0)    Degree: 7/6   (7/12, 7/12)
              [7]  xb_(0, 1/2, 1/2)    Degree: 7/6   (7/12, 7/12)
              [8]  y*zb_(0, 0, 0)      Degree: 4/3   (2/3, 2/3)
              [9]  x^2*y^2b_(0, 0, 0)  Degree: 5/3   (5/6, 5/6)
             [10]  x^2b_(0, 1/2, 1/2)  Degree: 5/3   (5/6, 5/6)
             [11]  x*y*zb_(0, 0, 0)    Degree: 11/6  (11/12, 11/12)
             [12]  x^2*y*zb_(0, 0, 0)  Degree: 7/3   (7/6, 7/6)
            sage: (2*B[3]+B[4]).degree
            2/3
            sage: (B[3]+B[9]).degree
            Warning: this element is not homogeneous.
            5/3
            
            sage: W = QSingularity.create("L35")
            sage: G = SymmetryGroup(W, "max")
            sage: A = FJRWRing(G)
            FJRW ring for x^3*y + x*y^5 with group generated by <(1/14, 11/14)>.
            Dimension:   15
            Basis:
              [1]  e_(2/7, 1/7)     Degree: 0     (0, 0)
              [2]  e_(3/14, 5/14)   Degree: 2/7   (1/7, 1/7)
              [3]  e_(1/7, 4/7)     Degree: 4/7   (2/7, 2/7)
              [4]  e_(9/14, 1/14)   Degree: 4/7   (2/7, 2/7)
              [5]  e_(1/14, 11/14)  Degree: 6/7   (3/7, 3/7)
              [6]  e_(4/7, 2/7)     Degree: 6/7   (3/7, 3/7)
              [7]  y^4e_(0, 0)      Degree: 8/7   (4/7, 4/7)
              [8]  x^2e_(0, 0)      Degree: 8/7   (4/7, 4/7)
              [9]  e_(1/2, 1/2)     Degree: 8/7   (4/7, 4/7)
            ...
            sage: A[4].degree
            4/7
            sage: A[8].degree
            8/7
            
            sage: W = QSingularity.create("x^3+x*y^5+y*z^2")
            C253
            [z, y, x]
            sage: G = SymmetryGroup(W, "J")
            sage: A = FJRWRing(G)
            FJRW ring for x^3 + x*y^5 + y*z^2 with group generated by <(2/3, 1/15, 29/30)>.
            Dimension:   21
            Basis:
              [1]  e_(1/3, 2/15, 13/30)   Degree: 0     (0, 0)
              [2]  e_(1/3, 1/3, 1/3)      Degree: 1/5   (1/10, 1/10)
              [3]  e_(1/3, 8/15, 7/30)    Degree: 2/5   (1/5, 1/5)
              [4]  e_(2/3, 1/15, 7/15)    Degree: 3/5   (3/10, 3/10)
              [5]  e_(1/3, 11/15, 2/15)   Degree: 3/5   (3/10, 3/10)
              [6]  e_(2/3, 4/15, 11/30)   Degree: 4/5   (2/5, 2/5)
              [7]  e_(1/3, 14/15, 1/30)   Degree: 4/5   (2/5, 2/5)
              [8]  e_(1/3, 2/15, 14/15)   Degree: 1     (1/2, 1/2)
              [9]  e_(2/3, 7/15, 4/15)    Degree: 1     (1/2, 1/2)
            ...
             [21]  e_(2/3, 13/15, 17/30)  Degree: 12/5  (6/5, 6/5)
            sage: A[2].degree
            1/5
            sage: A[8].degree
            1
            
            sage: W = QSingularity.create("C352")
            sage: G = SymmetryGroup(W, "max")
            sage: A = FJRWRing(G)
            FJRW ring for x^3*y + y^5*z + z^2 with group generated by <(1/30, 9/10, 1/2)>.
            Dimension:   17
            Basis:
              [1]  e_(3/10, 1/10, 1/2)   Degree: 0      (0, 0)
              [2]  e_(7/30, 3/10, 1/2)   Degree: 4/15   (2/15, 2/15)
              [3]  e_(1/6, 1/2, 1/2)     Degree: 8/15   (4/15, 4/15)
              [4]  e_(19/30, 1/10, 1/2)  Degree: 2/3    (1/3, 1/3)
              [5]  e_(1/10, 7/10, 1/2)   Degree: 4/5    (2/5, 2/5)
              [6]  y^4e_(1/3, 0, 0)      Degree: 13/15  (13/30, 13/30)
              [7]  e_(17/30, 3/10, 1/2)  Degree: 14/15  (7/15, 7/15)
              [8]  e_(1/30, 9/10, 1/2)   Degree: 16/15  (8/15, 8/15)
              [9]  e_(1/2, 1/2, 1/2)     Degree: 6/5    (3/5, 3/5)
            ...
            sage: A[8].degree
            16/15
            sage: A[5].degree
            4/5
            
            sage: W = QSingularity.create("C45")
            sage: G = SymmetryGroup(W, "max")
            sage: A = FJRWRing(G)
            FJRW ring for x^4*y + y^5 with group generated by <(1/20, 4/5)>.
            Dimension:   17
            Basis:
              [1]  e_(1/5, 1/5)    Degree: 0      (0, 0)
              [2]  e_(3/20, 2/5)   Degree: 3/10   (3/20, 3/20)
              [3]  e_(9/20, 1/5)   Degree: 1/2    (1/4, 1/4)
              [4]  e_(1/10, 3/5)   Degree: 3/5    (3/10, 3/10)
              [5]  e_(2/5, 2/5)    Degree: 4/5    (2/5, 2/5)
              [6]  e_(1/20, 4/5)   Degree: 9/10   (9/20, 9/20)
              [7]  e_(7/10, 1/5)   Degree: 1      (1/2, 1/2)
              [8]  e_(7/20, 3/5)   Degree: 11/10  (11/20, 11/20)
              [9]  x^3e_(0, 0)     Degree: 6/5    (3/5, 3/5)
             [10]  e_(13/20, 2/5)  Degree: 13/10  (13/20, 13/20)
            ...
            sage: A[9].degree
            6/5
            sage: A[1].degree
            0
            
            sage: W = QSingularity.create("C78")
            sage: G = SymmetryGroup(W, [[1/2,1/2]])
            sage: B = OrbMilnorRing(G)
            Orbifold Milnor ring for x^7*y + y^8 with group generated by <(1/2, 1/2)>.
            Dimension:   26
            Basis:
              [1]  b_(0, 0)         Degree: 0    (0, 0)
              [2]  y^2b_(0, 0)      Degree: 1/2  (1/4, 1/4)
              [3]  x*yb_(0, 0)      Degree: 1/2  (1/4, 1/4)
              [4]  x^2b_(0, 0)      Degree: 1/2  (1/4, 1/4)
              [5]  y^4b_(0, 0)      Degree: 1    (1/2, 1/2)
            ...
            sage: B[1].degree
            0
            sage: B[2].degree
            1/2
            sage: B[5].degree
            1
        
        """
        if not self.is_homogeneous:
            print("Warning: this element is not homogeneous.")
        return max([ elem.degree for elem in self.support() ])
        #Implementation of degree found in QuantumRingBasisElement
        
    @lazy_attr
    def bi_degree(self):
        """
        Return the bi-degree of this :class:`~QuantumRing.QuantumRingElement`.
        
        OUTPUT:
        
        - A tuple of rational numbers giving the bi-degree of this
          :class:`~!QuantumRing.QuantumRingElement`. The bi-degree is the
          maximum of the bi-degrees of the basis elements appearing with nonzero
          coefficients in a linear combination describing self. Here, comparison
          between tuples is as automatically implemented in Sage. A warning is
          printed if self is not bi-homogeneous.
        
        .. NOTE::
        
            The calculation for the bi-grading is given on page 13 of [Kr]_.
        
        EXAMPLES:
        
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G, print_basis=False)
            sage: B.print_summary()
            Orbifold Milnor ring for x^4 + y^3*z + z^2 with group generated by <(0, 1/2, 1/2)>.
            Dimension:   12
            Basis:
              [1]  b_(0, 0, 0)         Degree: 0     (0, 0)
              [2]  xb_(0, 0, 0)        Degree: 1/2   (1/4, 1/4)
              [3]  y^2b_(0, 0, 0)      Degree: 2/3   (1/3, 1/3)
              [4]  b_(0, 1/2, 1/2)     Degree: 2/3   (1/3, 1/3)
              [5]  x^2b_(0, 0, 0)      Degree: 1     (1/2, 1/2)
              [6]  x*y^2b_(0, 0, 0)    Degree: 7/6   (7/12, 7/12)
              [7]  xb_(0, 1/2, 1/2)    Degree: 7/6   (7/12, 7/12)
              [8]  y*zb_(0, 0, 0)      Degree: 4/3   (2/3, 2/3)
              [9]  x^2*y^2b_(0, 0, 0)  Degree: 5/3   (5/6, 5/6)
             [10]  x^2b_(0, 1/2, 1/2)  Degree: 5/3   (5/6, 5/6)
             [11]  x*y*zb_(0, 0, 0)    Degree: 11/6  (11/12, 11/12)
             [12]  x^2*y*zb_(0, 0, 0)  Degree: 7/3   (7/6, 7/6)
            sage: (2*B[3]+B[4]).bi_degree
            (1/3, 1/3)
            sage: (B[3]+B[9]).bi_degree
            Warning: this element is not homogeneous.
            (5/6, 5/6)
            
            sage: W = QSingularity.create("L555")
            sage: G = SymmetryGroup(W, "J")
            sage: A = FJRWRing(G)
            FJRW ring for x^5*y + x*z^5 + y^5*z with group generated by <(1/6, 1/6, 1/6)>.
            Dimension:   25
            Basis:
            ...
              [8]  x*y*ze_(0, 0, 0)        Degree: 2  (1/2, 3/2)
              [9]  x*y^2e_(0, 0, 0)        Degree: 2  (1/2, 3/2)
             [10]  x^2*ze_(0, 0, 0)        Degree: 2  (1/2, 3/2)
             [11]  x^2*ye_(0, 0, 0)        Degree: 2  (1/2, 3/2)
             [12]  x^3e_(0, 0, 0)          Degree: 2  (1/2, 3/2)
             [13]  e_(1/2, 1/2, 1/2)       Degree: 2  (1, 1)
             [14]  x*y^4*z^4e_(0, 0, 0)    Degree: 2  (3/2, 1/2)
            ...
            sage: A[8].bi_degree
            (1/2, 3/2)
            sage: A[13].bi_degree
            (1, 1)
            sage: A[14].bi_degree
            (3/2, 1/2)
        
        """
        if not self.is_bi_homogeneous:
            print("Warning: this element is not homogeneous.")
        return max([ elem.bi_degree for elem in self.support() ])

        #Implementation of bi_degree for the A-model is found in FJRW.py and
        #implemenation of bi_degree for the B-model is found in OrbMilnor.py
        
    def _to_dict(self):
        """
        Return a dictionary with integer keys and values describing self. This is used to store self more compactly in the product database.
        
        OUTPUT:
        
        - A dictionary whose keys are the indices of the basis elements appearing in the support of self, and whose values are the corresponding coefficients.
        
        This should be the inverse for the parent's method _create_element_from_dict::
        
            sage: from LGModels import *
            sage: W = QSingularity.create("f52")
            sage: G = SymmetryGroup(W)
            sage: B = OrbMilnorRing(G, print_basis = False)
            sage: a,b,c,d = B.list()
            sage: B._create_elem_from_dict(a._to_dict())==a
            True
            
        """
        data = self.monomial_coefficients()
        # If self is a rational linear combination of basis elements, 
        # we convert the coefficients to rationals. Depending on the coefficient
        # ring of the parent, they may be something else, like Expressions.
        # This method is use to save the products dictionary. By making the
        # coefficients rationals when possible, we allow this dictionary to be
        # loaded by QuantumRings with a different coefficient ring.
        try:
            return dict([ (monom.index, QQ(data[monom]) ) for monom in data ])
        except ValueError:
            # In this case, one of the coefficients was not a rational
            return dict([ (monom.index, data[monom] ) for monom in data ])
            
    @lazy_attr
    def in_basis(self):
        """
        Return True if self is a basis element.
        
        Examples::
        
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G, print_basis=False)
            sage: B[1].in_basis
            True
            sage: (B[1] - B[2]).in_basis
            False
            sage: (-3*B[1]).in_basis
            False
            sage: (1*B[1]).in_basis
            True
            sage: B.zero().in_basis
            False
        
        """
        # try:
#             normalized = self/self.leading_coefficient()
#         except ValueError:
#         # In this case, self must be zero
#             return ( self in self.parent().basis() )
#         return ( normalized in self.parent().basis() )
        return ( self in self.parent().basis() )

    #check if all basis elements come from the same sector
    @lazy_attr
    def sector(self):
        """
        Return the sector of this ring element. If every basis element of 
        self is in the same sector, return that sector; otherwise raise
        a NotImplementedError.
  
        Examples::
        
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G, print_basis=False)
            sage: a, b, c  = B[2], B[3], B[4]
            sage: a; b; c
            xb_(0, 0, 0)
            y^2b_(0, 0, 0)
            b_(0, 1/2, 1/2)
            sage: a.sector
            (0, 0, 0)
            sage: (a + 3 * b).sector
            (0, 0, 0)
            sage: (a - c).sector
            Traceback (most recent call last):
            ...
            NotImplementedError: This method is only implemented for elements that are linear combinations of basis elements from the same sector.
            
        """
        if self.in_basis:
            return self.leading_support().sector
        else:
            my_sectors = set([ elem.sector for elem in self.support() ])
            if len(my_sectors) == 1:
                return my_sectors.pop()
            else:
                raise NotImplementedError("This method is only implemented for elements that are linear combinations of basis elements from the same sector.")
            
    @lazy_attr
    def monomial(self):
        """
        Return the monomial of this ring element. If self is a
        basis element, return the corresponding monomial; otherwise raise a
        NotImplementedError.

        Examples::
        
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G, print_basis=False)
            sage: b = B[3]; b
            y^2b_(0, 0, 0)
            sage: b.monomial
            y^2
            sage: (2*b).monomial
            Traceback (most recent call last):
            ...
            NotImplementedError: This method is only implemented for basis elements.
             
        """
        if self.in_basis:
            return self.leading_support().monomial
        else:
            raise NotImplementedError("This method is only implemented for basis elements.")
    
    @lazy_attr
    def is_homogeneous(self):
        """
        Return True if self is a linear combination of basis elements of the
        same degree.
        
        EXAMPLES:
            
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G, print_basis=False)
            sage: B.print_summary()
            Orbifold Milnor ring for x^4 + y^3*z + z^2 with group generated by <(0, 1/2, 1/2)>.
            Dimension:   12
            Basis:
              [1]  b_(0, 0, 0)         Degree: 0     (0, 0)
              [2]  xb_(0, 0, 0)        Degree: 1/2   (1/4, 1/4)
              [3]  y^2b_(0, 0, 0)      Degree: 2/3   (1/3, 1/3)
              [4]  b_(0, 1/2, 1/2)     Degree: 2/3   (1/3, 1/3)
              [5]  x^2b_(0, 0, 0)      Degree: 1     (1/2, 1/2)
              [6]  x*y^2b_(0, 0, 0)    Degree: 7/6   (7/12, 7/12)
              [7]  xb_(0, 1/2, 1/2)    Degree: 7/6   (7/12, 7/12)
              [8]  y*zb_(0, 0, 0)      Degree: 4/3   (2/3, 2/3)
              [9]  x^2*y^2b_(0, 0, 0)  Degree: 5/3   (5/6, 5/6)
             [10]  x^2b_(0, 1/2, 1/2)  Degree: 5/3   (5/6, 5/6)
             [11]  x*y*zb_(0, 0, 0)    Degree: 11/6  (11/12, 11/12)
             [12]  x^2*y*zb_(0, 0, 0)  Degree: 7/3   (7/6, 7/6)
            sage: (2*B[3]+B[4]).is_homogeneous
            True
            sage: (B[3]+B[9]).is_homogeneous
            False
            
        """
        my_degrees = set([ elem.degree for elem in self.support() ])
        return ( len(my_degrees) == 1 )
        
    @lazy_attr
    def is_bi_homogeneous(self):
        """
        Return True if self is a linear combination of basis elements of the
        same bi-degree.
        
        EXAMPLES:
            
            sage: from LGModels import *
            sage: W = Qs("F4C32")
            sage: G = Grp(W, [[0, 1/2, 1/2]])
            sage: B = Bm(G, print_basis=False)
            sage: B.print_summary()
            Orbifold Milnor ring for x^4 + y^3*z + z^2 with group generated by <(0, 1/2, 1/2)>.
            Dimension:   12
            Basis:
              [1]  b_(0, 0, 0)         Degree: 0     (0, 0)
              [2]  xb_(0, 0, 0)        Degree: 1/2   (1/4, 1/4)
              [3]  y^2b_(0, 0, 0)      Degree: 2/3   (1/3, 1/3)
              [4]  b_(0, 1/2, 1/2)     Degree: 2/3   (1/3, 1/3)
              [5]  x^2b_(0, 0, 0)      Degree: 1     (1/2, 1/2)
              [6]  x*y^2b_(0, 0, 0)    Degree: 7/6   (7/12, 7/12)
              [7]  xb_(0, 1/2, 1/2)    Degree: 7/6   (7/12, 7/12)
              [8]  y*zb_(0, 0, 0)      Degree: 4/3   (2/3, 2/3)
              [9]  x^2*y^2b_(0, 0, 0)  Degree: 5/3   (5/6, 5/6)
             [10]  x^2b_(0, 1/2, 1/2)  Degree: 5/3   (5/6, 5/6)
             [11]  x*y*zb_(0, 0, 0)    Degree: 11/6  (11/12, 11/12)
             [12]  x^2*y*zb_(0, 0, 0)  Degree: 7/3   (7/6, 7/6)
            sage: (2*B[3]+B[4]).is_bi_homogeneous
            True
            sage: (B[3]+B[9]).is_bi_homogeneous
            False
            
        """
        my_degrees = set([ elem.bi_degree for elem in self.support() ])
        return ( len(my_degrees) == 1 )
            
        
    @lazy_attr
    def index(self):
        """
        Return an integer `i` so that `B[i]` returns self. Return a Python :class:`int` (and can therefore be used in things like
        string formatting).
        
        .. TODO::
        
            Add tests.
        
        """
        if self.in_basis:
            return self.leading_support().index
        else:
            raise NotImplementedError("This is only implemented for basis elements.")
        
      

#     def factor(self):
#         """
#         Return a tuple of a scalar and two :class:`~myAlgebra.AlgebraElem`
#         instances whose product is this basis element, if they can be found.
#         Returns ``None`` if none can be found. Since we are not guaranteed to
#         be able to compute all the multiplications, in general a return of
#         ``None`` does not guarantee that this class is not primitive.
#         
#         .. TODO::
#         
#             Add tests.
#         
#         """
#         self.myRing.find_nonprimitive()
#         if self.__dict__.has_key("factor_scalar"):
#             return (self.factor_scalar, self.factor1, self.factor2)
#         return None
#     
#     def record_factorization(self, a1, a2, scalar):
#         """
#         Specify that the element can be decomposed as ``scalar`` `\cdot` ``a1``
#         `\star` ``a2``.
#         
#         Called by :meth:`~QuantumRing.QuantumRing.find_nonprimitive`.
#         
#         .. TODO::
#         
#             Add tests.
#         
#         """
#         
#         self.factor1 = a1
#         self.factor2 = a2
#         self.factor_scalar = scalar
  
        
class QuantumRingBasisElement(UniqueRepresentation):
    """
    Abstract base class for :class:`~FJRW.FJRWBasisElement` and
    :class:`~OrbMilnor.OrbMilnorBasisElement`. These are assigned to
    the attribute `_my_basis_element` of :class:`~FJRW.FJRWRing` and :class:`~OrbMilnor.OrbMilnorRing`,
    respectively.
    
    CONSTRUCTOR:
    
    - ``parent_ring`` -- The :class:`~QuantumRing.QuantumRing` to which this basis element belongs.
    - ``monomial`` -- The milnor ring basis element associated with this basis element.
    - ``sector`` -- A :class:`~SymmetryGroup.SymmetryGroupElement` associated to this
        basis element.
    
    .. NOTE::
    
        Elements of this class are basis elements for a QuantumRing. The user
        should not call this constructor directly. In fact, the user should never use
        instances of this class directly. Instead, all elements of a QuantumRing
        will be QuantumRingElements. See the documentation at the beginning of QuantumRing.py for more details.
    
    """

    def __init__(self, parent_ring, monomial, sector):
        
        self.parent_ring = parent_ring
        """The :class:`~QuantumRing.QuantumRing` to which this basis element belongs."""
        
        self.monomial = monomial
        """The milnor ring basis element associated with this basis element."""
        
        self.sector = sector
        """A :class:`~SymmetryGroup.SymmetryGroupElement` associated to this
        basis element."""
        
        self.index = None
        """An integer `i` such that self.parent_ring[i] returns self."""
        self._factors = None
        
        """A list of known factors of self. Set in self.parent().products(). See alse QuantumRingElement.factor()."""
        
        if monomial == 1:
            self.name = "".join([self.parent_ring._basis_element_repr, "_", repr(sector)])
            """A string giving the long name of this basis element. Includes the
            associated monomial and group element. Used by
            :meth:`~QuantumRing.QuantumRingElement._repr_`."""
        else:
            self.name = "".join([repr(monomial),
                                 self.parent_ring._basis_element_repr, "_", repr(sector)])

    def __repr__(self):
        """
        Return :attr:`self.name <QuantumRing.QuantumRingBasisElement.name>`, a string
        giving an unambiguous representation of ``self``, including
        :attr:`self.monomial <QuantumRing.BasisElement.monomial>` and
        :attr:`self.sector <QuantumRing.BasisElement.sector>`.
        
        .. TODO::
        
            Add tests.
        
        """
        return self.name
        
    def __str__(self):
        """
        Return a string giving a simple, human-friendly version of ``self``.
        This string is the index of self in the parent's list of basis elements.
        
        .. TODO::
        
            Add tests.
        
        """
        return str(self.index)
       
    def _hash_(self):
        """
        Return the hash value of :attr:`self.name
        <QuantumRing.BasisElement.name>`.
        """
        return hash(self.name)
        
    def _latex_(self):
        """
        Return a string giving an appropriate LaTeX representation of ``self``.
        Called by the :func:`latex` function.
        
        .. TODO::
        
            Add tests.
        
        """
        return r"\kn{" + latex(self.monomial) + r"}{" + latex(self.sector) + r"}"
    
    @lazy_attr
    def is_narrow(self):
        """
        Return ``True`` if this is a narrow element; i.e., its group element
        has trivial fixed locus.
        
        .. TODO::
        
            Add tests.
        
        """
        return (len(self.sector.fixed) == 0)
    
    @lazy_attr
    def degree(self):
        """
        Return the appropriate degree of this
        :class:`~QuantumRing.QuantumRingBasisElement`.
        
        OUTPUT:
        
        - A rational number giving the degree of this
          :class:`~!QuantumRing.QuantumRingBasisElement`.
          
        .. NOTE::
        
            The degree is the sum of the bi-degrees. See pg 13 of [Kr]_.
        
        """
        return (self.bi_degree[0] + self.bi_degree[1])
        #degree method just adds the bi_degree of the basis element
        #Implemented in parent instead of subclass (Julian Tay, Dec 2012)
    
    @lazy_attr
    def bi_degree(self):
        """
        Return the bigrading of this :class:`~QuantumRing.QuantumRingBasisElement`.
        
        OUTPUT:
        
        - A tuple of rational numbers giving the bigrading of this
          :class:`~!QuantumRing.QuantumRingBasisElement`.
        
        .. NOTE::
        
            The calculation for the bi-grading is given on page 13 of [Kr]_.
        
        """
        raise NotImplementedError('Must be implemented in subclasses.')
        
    def __lt__(left, right):
        """
        Establish an ordering on the basis elements of a QuantumRing.
        
        When we compare two basis elements, we first compare their degrees,
        then their bi-degrees, then their sectors, and finally their monomials.
        
        .. WARNING::
        
            - This might conceivably say two basis elements are not equal when actually they are (in the milnor ring) - this depends on how good the __cmp__ method is on the monomials.
            - Changing the __cmp__ method on group elements or monomials will change
            this method as well.
            
        AUTHORS:
        
            - Rachel Suggs (September 2012)
        """
        if left.degree != right.degree:
            return left.degree< right.degree
        elif left.bi_degree != right.bi_degree:
            return left.bi_degree< right.bi_degree
        elif left.sector != right.sector:
            return left.sector< right.sector
        else:
            return left.monomial< right.monomial
            

    

class QuantumRing(CombinatorialFreeModule):
    """
    Abstract base class for :class:`~FJRW.FJRWRing` and
    :class:`~OrbMilnor.OrbMilnorRing`. Constructs the state space, provides the
    :meth:`interface for retrieving items
    <QuantumRing.QuantumRing.__getitem__>`, and a :meth:`method to print
    everything <QuantumRing.QuantumRing.print_summary>`. Also provides most of
    the structure for subclasses.
    
    CONSTRUCTOR:
    
    - ``Gsec`` -- The :class:`~SymmetryGroup.SymmetryGroup` that will create the
      sectors.
    - ``Ginv`` -- The :class:`~SymmetryGroup.SymmetryGroup` to take invariants
      by. Defaults to equal ``Gsec``.
    - ``print_basis`` -- If set to true, a summary of this ring will be printed
      upon construction. Defaults to True.
    - ``R`` -- The base ring of this algebra. Must be a field. Defaults to "QQ".
    - ``prefix`` -- A string that is the name of this ring. Defaults to "Q".
    - ``basis_element_repr`` -- A string used when printing out basis elements 
      of this class. Defaults to "q".
    
    .. NOTE::
    
        This is an abstract class and should not be instantiated directly. For usage
        examples, see subclasses.
        
    .. TODO::
    
        Try building rings with base rings other than QQ.
    
    """
   
    Element = QuantumRingElement
    """An alias for the class of elements of this ring. Must be redefined in the subclasses."""
    
    _ring_type = None
    """A string describing the type of ring that this is. Must be defined in
    subclasses."""
    
    _my_basis_element = QuantumRingBasisElement
    """An alias for the class of basis elements of this ring. Must be redefined in
    subclasses."""
    
    def __init__(self, Gsec, Ginv="default", print_basis = True, R=QQ, prefix = "Q", basis_element_repr = "q"):
        """Constructor -- see class documentation."""
        
        self.Gsec = Gsec
        """The :class:`~SymmetryGroup.SymmetryGroup` that will create the
        sectors."""
        
        self.Ginv = Ginv
        """The :class:`~SymmetryGroup.SymmetryGroup` to take invariants by."""
        
        self.singularity = Gsec.poly
        """The :class:`~Singularity.Singularity` used to create this FJRW
        ring."""
        
        self._basis_element_repr = basis_element_repr
        """The string to put in front of :class:`~QuantumRing.QuantumRingBasisElement`\
        s in their :meth:`~QuantumRing.QuantumRingBasisElement._repr_` method. Used to create
        :attr:`~QuantumRing.BasisElement.name`."""
        
        self._basis_element_string = prefix
        """The string to put in front of :class:`~QuantumRing.QuantumRingBasisElement`\
        s in their :meth:`~QuantumRing.QuantumRingBasisElement.__str__` method."""
        
        try:
            self.polystring = self.singularity.polystring
            """A string representing :attr:`self.singularity
            <QuantumRing.QuantumRing.singularity>` if it is invertible, else
            ``None``. The string is in the form passed to
            :meth:`~QSingularity.QSingularity.create`, i.e. ``L33C34``"""
        except AttributeError:
            self.polystring = None

        if str(self.Ginv) == "default":
            self.Ginv = self.Gsec
        elif Ginv.poly != self.singularity:
            raise ValueError("Invalid input: received groups from different polynomials.")
        
        # Check that the coefficient ring passed in is actually a field
        if not R.is_field():
            raise ValueError("Invalid input: R must be a field.")
        
        # Use compute method to make basis elements, and use these as the arguments to the constructor.
        elems = self._compute()
        super(QuantumRing, self).__init__(R, elems, category = GradedAlgebrasWithBasis(R), prefix = prefix)
        
        self.basis_by_name = dict(zip([repr(a) for a in self.list()], self.list() ))
        """A dictionary of the basis elements of self indexed by their string representations."""
        
        # We print a summary of this ring if requested.
        if print_basis:
            self.print_summary()
            
        # The construction of the state space ends here.
        
        # Load or create dictionaries to store data that we've already computed.
        # This feature added by Scott Mancuso, May 2012.
        try:
            self._products_dict = load(os.path.join(
                                            PRODUCTS_DICT_DIRECTORY,
                                            "%s" % self._file_safe_repr()))
            """A dictionary that stores the value of a product of basis elements
            each time it's computed. The key is a sorted tuple giving the
            indices of the basis elements. The value is the value of their
            product."""
        except IOError:
            # We've never created this ring before.
            self._products_dict = {}
        
        try:
            self._pairings_dict = load(os.path.join(
                                            PAIRINGS_DICT_DIRECTORY,
                                            "%s" % self._file_safe_repr()))
            """A dictionary that stores the value of a pairing of basis elements
            each time it's computed. The key is a sorted tuple giving the
            indices of the basis elements. The value is the value of their
            pairing."""
        except IOError:
            # We've never created this ring before.
            self._pairings_dict = {}
        
        if self._inside_doctest():
            # Don't modify the saved values if run by a doctest.
            self._products_dict_orig = self._products_dict
            self._products_dict = {}
            self._pairings_dict_orig = self._pairings_dict
            self._pairings_dict = {}
            # Check to make sure the newly computed values don't conflict with
            # the previously saved values.
            atexit.register(self._verify_products)
            atexit.register(self._verify_pairings)
        elif not self._inside_timeit():
            # Make sure to update the saved files when we close Sage.
            atexit.register(self._update_products_file)
            atexit.register(self._update_pairings_file)
        
        for indices, index_data in self._products_dict.items():
            # Replace each index with its actual ``BasisElement``.
            self._products_dict[indices] = (
                    self._create_elem_from_dict(index_data))
        
        # Hash the values of these dictionaries. We'll only re-save them if they
        # change; however, we don't want to lug around an entire extra copy of
        # each dictionary.
        self._products_hash = hash(tuple(self._products_dict.values()))
        self._pairings_hash = hash(tuple(self._pairings_dict.values()))

    def _repr_(self):
        """
        Return a string describing this :class:`~QuantumRing.QuantumRing`,
        including what type of ring it is and its associated singularity and
        group(s).
        
        .. TODO::
        
            Add tests.
        
        """
        rep = (self._ring_type + " for " + str(self.singularity)
               + " with group generated by " + str(self.Gsec))
        if self.Gsec != self.Ginv:
            rep += (" but with invariants taken with the group generated by G' "
                    "= " + str(self.Ginv))
        rep += "."
        return rep
    
    def _compute(self):
        """
        Return a list of basis elements of this ring. Called by the :class:`~QuantumRing.QuantumRing` constructor.
        These objects have their :attr:`self.index <QuantumRing.QuantumRingBasisElement.index>` attribute set
        according to their place in the list returned.
        
        OUTPUT:

        - A list of class:`~QuantumRing.QuantumRingBasisElement` objects.

        .. TODO::
        
            Describe what this function does and how it does it more explicitly.
        
        EXAMPLES:
        
        We want to make sure that the index of each item is set correctly::
        
            sage: from LGModels import *
            sage: W = QSingularity.create("C34F6")
            sage: G = SymmetryGroup(W, "J")
            sage: Gt = G.transpose()
            sage: H = FJRWRing(G, print_basis=False)
            sage: B = OrbMilnorRing(Gt, print_basis=False)
            
            sage: for basis_elem, index in zip(H.list(),
            ...                                xrange(1, H.dimension() + 1)):
            ...       assert basis_elem.index == index, (
            ...              "Item %(index)d in the H.basis failed" % locals())
            ...
            
            sage: for basis_elem, index in zip(B.list(),
            ...                                xrange(1, B.dimension() + 1)):
            ...       assert basis_elem.index == index, (
            ...              "Item %(index)d in the B.basis failed" % locals())
            ...
        
        """

        basis_elems = []
        for g in self.Gsec:
            # Wfixg is the singularity (polynomial) restricted to the fixed
            # locus of g.
            Wfixg = self.singularity.restrict(g.fixed)
            # If Wfixg == 0, then we add monomial "1" in the "g"-sector.
            if Wfixg.is_zero():
                basis_elems.append(self._my_basis_element(self, 1, g))
            else:
                # Find the restricted Milnor ring basis.
                Hg = Wfixg.milnor_ring
                for m in Hg:
                    if self.Ginv.is_invariant(g, m):
                        basis_elems.append(self._my_basis_element(self, m, g))

        # Now we set the index of each basis element
        basis_elems.sort()
        for index in range(len(basis_elems)):
            basis_elem = basis_elems[index]
            basis_elem.index = index + 1 # use 1-based indexing

        return basis_elems
    
    def _file_safe_repr(self):
        """
        Get a version of ``self`` that is acceptable as a file name. It does not
        depend on the names given to the variables of :attr:`self.singularity
        <QuantumRing.QuantumRing.singularity>`. This is so that the next time we
        create this ring, it doesn't matter whether or not we use the same
        variable names; the database files will be properly loaded either way.
        
        OUTPUT:
        
        - A string with spaces and slashes replaced by underscores and all
          variable names replaced by ``X1,..., XN``.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: W = QSingularity.create("L23F3")
            sage: G = SymmetryGroup(W, "max")
            sage: H = FJRWRing(G, print_basis=False); H
            FJRW ring for x^2*y + x*y^3 + z^3 with group generated by <(2/5,
            1/5, 1/3)>.
            sage: print H._file_safe_repr()
            FJRW_ring_X1^2*X2_+_X1*X2^3_+_X3^3_<(2_5,_1_5,_1_3)>
            
        Different variable names give the same result::
        
            sage: Wbar = QSingularity.create("L23F3", ["xbar", "ybar", "zbar"])
            sage: Gbar = SymmetryGroup(Wbar, "max")
            sage: Hbar = FJRWRing(Gbar, print_basis=False)
            sage: H._file_safe_repr() == Hbar._file_safe_repr()
            True
        
        Using :class:`~Singularity.Singularity` also works::
        
            sage: R.<y, z, x> = QQ[]
            sage: Wsing = Singularity.create(y^2*z + y*z^3 + x^3)
            sage: Gsing = SymmetryGroup(Wsing, "max")
            sage: Hsing = FJRWRing(Gsing, print_basis=False)
            sage: H._file_safe_repr() == Hsing._file_safe_repr()
            True
        
        .. TODO::
        
            Add tests, including to make sure that the same singularity gives
            the same result, even if it was created by
            :meth:`~QSingularity.QSingularity.icreate`.
        
        AUTHOR:
        
        - Scott Mancuso (June 2012)
        
        """
        W = self.singularity
        Ws = str(W)
        for i, j in zip(W.vars, range(1, W.nvariables + 1)):
            Ws = Ws.replace(str(i), "X%d" % j)

        rep = "_".join([self._ring_type, Ws, str(self.Gsec)])
        if self.Gsec != self.Ginv:
            rep += "_" + str(self.Ginv)
        return rep.replace(" ", "_").replace("/", "_")
    
    def _update_products_file(self):
        """
        Update the saved file to reflect recently computed products. If called
        from inside a doctest or timing function, or if no new products have
        been computed since this ring was created, it simply exits without
        updating the saved file. Doesn't return a value.
        
        In order to save time and space, the values in
        :attr:`~QuantumRing.QuantumRing._products_dict` are converted from
        :class:`~myAlgebra.AlgebraElem` s to dictionaries of integers before
        being saved to the hard drive.
        
        .. TODO::
        
            Add tests.
        
        AUTHOR:
        
        - Scott Mancuso (June 2012)
        
        """
        products_hash = hash(tuple(self._products_dict.values()))
        if self._products_hash == products_hash:
            # `_products_dict` hasn't changed, so don't save it again.
            return
        else:
            self._products_hash = products_hash
        if self._inside_doctest() or self._inside_timeit():
            return
        
        # Convert `AlgebraElem`s to dictionaries of integers in order to save
        # space and time.
        index_products_dict = {}
        for indices, product in self._products_dict.items():
            try:
                index_products_dict[indices] = product._to_dict()
            except AttributeError:
                # We got a CouldNotComputeException. This gets saved as is.
                index_products_dict[indices] = product
        save(index_products_dict, os.path.join(PRODUCTS_DICT_DIRECTORY,
                                              "%s" % self._file_safe_repr()))
        print("Products updated.")

    def _update_pairings_file(self):
        """
        Update the saved file to reflect recently computed pairings. If called
        from inside a doctest or timing function, or if no new pairings have
        been computed since this ring was created, it simply exits without
        updating the saved file. Doesn't return a value.
        
        .. TODO::
        
            Add tests.
        
        AUTHOR:
        
        - Scott Mancuso (June 2012)
        
        """
        pairings_hash = hash(tuple(self._pairings_dict.values()))
        if self._pairings_hash == pairings_hash:
            # `_pairings_dict` hasn't changed, so don't save it again.
            return
        else:
            self._pairings_hash = pairings_hash
        if self._inside_doctest() or self._inside_timeit():
            return
        save(self._pairings_dict, os.path.join(PAIRINGS_DICT_DIRECTORY,
                                                "%s" % self._file_safe_repr()))
        print("Pairings updated.")
    
    @lazy_attr
    def sectors(self):
        """
        Return a dictionary whose keys are the bigradings and whose values are
        lists of basis elements with those bigradings.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: G = SymmetryGroup(QSingularity.create("c324"),[[1/4,1/4,1/2]]) 
            sage: B = OrbMilnorRing(G, print_basis = False)
            sage: B.sectors
            {(0, 0): [b_(0, 0, 0)], (5/6, 5/6): [x*y*zb_(0, 0, 0)], (1/6, 7/6): [b_(1/4, 1/4, 1/2)], (4/3, 4/3): [x*y*z^3b_(0, 0, 0)], (7/6, 1/6): [b_(3/4, 3/4, 1/2)], (2/3, 2/3): [x^2*zb_(0, 0, 0), zb_(1/2, 1/2, 0)], (1/2, 1/2): [z^2b_(0, 0, 0)]}
        
        """
        sectors = {}
        for b in self.list():
            try:
                sectors[b.bi_degree].append(b)
            except KeyError:
                sectors[b.bi_degree] = [b]
        
        return sectors
            

    def print_summary(self):
        """
        Print a summary of the state space. Prints each element and its degree.
        Basis elements are sorted first by degree, then by bi-grading. Does not
        retun a value.
        
        EXAMPLE::
            
            sage: from LGModels import *
            sage: W = QSingularity.create("c324")
            sage: G = SymmetryGroup(W, [[1/4, 1/4, 1/2]])
            sage: B = Bm(G)
            Orbifold Milnor ring for x^3*y + y^2*z + z^4 with group generated by
            <(1/4, 1/4, 1/2)>.
            Dimension:   8
            Basis:
              [1]  b_(0, 0, 0)         Degree: 0    (0, 0)
              [2]  z^2b_(0, 0, 0)      Degree: 1    (1/2, 1/2)
              [3]  b_(1/4, 1/4, 1/2)   Degree: 4/3  (1/6, 7/6)
              [4]  x^2*zb_(0, 0, 0)    Degree: 4/3  (2/3, 2/3)
              [5]  zb_(1/2, 1/2, 0)    Degree: 4/3  (2/3, 2/3)
              [6]  b_(3/4, 3/4, 1/2)   Degree: 4/3  (7/6, 1/6)
              [7]  x*y*zb_(0, 0, 0)    Degree: 5/3  (5/6, 5/6)
              [8]  x*y*z^3b_(0, 0, 0)  Degree: 8/3  (4/3, 4/3)
            
        """
        max_length = max([len(repr(b)) for b in self.list()])
        max_degree_length = max([len(repr(b.degree)) for b in self.list()])
        print(repr(self))
        print("Dimension:  ", self.dimension())
        print("Basis:")
        for b, index in zip(self.list(), range(1, len(self.list()) + 1)):
            print(("[%(index)s]" % locals()).rjust(5) + "  " +
                  repr(b).ljust(max_length + 2) + "Degree: " +
                  repr(b.degree).ljust(max_degree_length + 2) +
                  repr(b.bi_degree))
    

    
    def products(self, unknowns=True, print_to_screen=True):
        """
        Compute all products and print a summary of all those that are
        nontrivial and nonzero.
        
        INPUT:
        
        - ``unknowns`` -- A boolean saying whether or not to print products that
          couldn't be computed. Defaults to ``True``.
        - ``print_to_screen`` -- A boolean saying whether to print the products
          or simply compute them. The advantage of not printing them is that you
          can populate :attr:`self._products_dict
          <QuantumRing.QuantumRing._products_dict>` quickly without printing
          lots of output. Defaults to ``True``.
        
        Does not return a value.
        
        .. TODO::
        
            Add tests.
        
        AUTHORS:
        
        - Amanda Francis (May 2012)
        
          - Main author.
          
        - Scott Mancuso (June 2012)
        
          - Moved from :class:`~FJRW.FJRWRing` to
            :class:`~QuantumRing.QuantumRing`.
          - Refactored to improve speed.
        
        """
        product_strings = []
        A = self._basis_element_string
        for b1 in range(0, self.dimension()):
            for b2 in range(len(self.list()[b1:])):
                factor1 = self.list()[b1]
                factor2 = self.list()[b2 + b1]
                #print factor1, factor2
                try:
                    answer = factor1 * factor2
                except CouldNotComputeException:
                    if unknowns and print_to_screen:
                        product_strings.append("%s * %s = ???"
                                               % (str(factor1), str(factor2)))
                    continue
                
                # We are not interested in products that are 0
                # Here we set the ._factors attribute of the basis elements.
                if answer != 0 and (answer/answer.leading_coefficient()).in_basis:
                    scalar = answer.leading_coefficient()
                    basis_elem = answer.leading_support()
                    try:
                        basis_elem._factors.append((1/scalar, factor1, factor2))
                    except AttributeError:
                        # In this case we hadn't yet found a factorization for this element
                        basis_elem._factors = [(1/scalar, factor1, factor2)]
                # Now we  print as requested.
                # We do not print products involving the identity or products that are 0.
                if print_to_screen and b1 > 0 and answer !=0:
                    product_strings.append("%s * %s = %s"
                                               % (str( factor1 ), str( factor2 ), str( answer )))
        if print_to_screen:
            print("\n".join(product_strings))
        
        #self._update_products_file()
        #self._update_pairings_file()
        #try:
        #    self._update_corrs_file()
        #except AttributeError:
        #    # This isn't an FJRWRing.
        #    pass
     
    def pairings(self, print_to_screen=True):
        """
        Compute all pairings and print a summary of all those that are nonzero.
        
        INPUT:
        
        - ``print_to_screen`` -- A boolean saying whether to print the pairings
          or simply compute them. The advantage of not printing them is that you
          can populate :attr:`self._pairings_dict
          <QuantumRing.QuantumRing._pairings_dict>` quickly without printing
          lots of output. Defaults to ``True``.
        
        Does not return a value.
        
        .. TODO::
        
            Add tests.
        
        AUTHORS:
        
        - Scott Mancuso (October 2013)
        
          - Modified :meth:`~QuantumRing.QuantumRing.products` since pairings
            are not computed on the B-side when products are computed, so a
            specific method is necessary.
        
        """
        pairing_strings = []
        A = self._basis_element_string
        for b1 in range(0, self.dimension()):
            for b2 in range(len(self.list()[b1:])):
                factor1 = self.list()[b1]
                factor2 = self.list()[b2 + b1]
                #print factor1, factor2
                answer = self.pair(factor1, factor2)
                
                # Now we  print as requested.
                # We do not print products involving the identity or products
                # that are 0.
                if print_to_screen and answer != 0:
                    pairing_strings.append("<{}, {}> = {}".format(factor1, 
                                                                  factor2,
                                                                  answer))
        if print_to_screen:
            print("\n".join(pairing_strings))
        
        self._update_pairings_file()
    
    @lazy_attr
    def eta(self):
        """
        Return the pairing matrix for this :class:`~QuantumRing.QuantumRing`.
        
        OUTPUT:
        
        - A symmetric square matrix over the base ring of
          :attr:`self.singularity <QuantumRing.QuantumRing.singularity>` whose
          ``[i, j]`` th entry is the value of the pairing of the ``i`` th and
          ``j`` th elements of the basis of self.
        
        .. TODO::
        
            Add tests.
        
        """
        
        mu2 = self.dimension()
        eta = Matrix(self.singularity.poly.parent().base_ring(), mu2)
        for i in range(0, mu2):
            for j in range(i, mu2):
                eta[i, j] = self.pair(self.list()[i], self.list()[j])
                eta[j, i] = eta[i, j]  #the pairing is symmetric
        return eta
        
    @lazy_attr
    def eta_inv(self):
        """
        Return the inverse pairing matrix for this
        :class:`~QuantumRing.QuantumRing`.
        
        OUTPUT:
        
        - A symmetric square matrix that is the inverse of :meth:`self.eta
          <QuantumRing.QuantumRing.eta>`.
        
        .. TODO::
        
            Add tests.
        
        """
        return self.eta.inverse()
        
    def pair(self, a, b):
        """
        Return the pairing of ``a`` and ``b``.
        
        INPUT:
        
        - ``a, b`` -- Two members of the element class of self.
        
        OUTPUT:
        
        - The value of the pairing of ``a`` and ``b``.
        
        .. TODO::
        
            Add tests.
        
        """
        if not a.parent() == b.parent():
            raise TypeError("unsupported operand parent(s) for '*':"+repr(a.parent())+repr(b.parent()) ) 
        a_dict = a.monomial_coefficients()
        b_dict = b.monomial_coefficients()
        single_pairings = cartesian_product([list(a_dict.keys()),list(b_dict.keys())])
        ll = [ai for (ai,bi) in single_pairings]
        return sum([ a_dict[ai]*b_dict[bi]*self.pairing_on_basis( ai, bi ) for (ai, bi) in single_pairings ])
     
    def pairing_on_basis(self, x, y ):
        """
        Return the pairing of ``a`` and ``b``.
        
        INPUT:
        
        - ``a, b`` -- Two :class:`~QuantumRing.QuantumRingBasisElement` s that are in the basis of self.
        
        OUTPUT:
        
        - The value of the pairing of ``a`` and ``b``.
        
        .. NOTE::
            
            This method is called by the method :meth:`~QuantumRing.QuantumRing.pair`.
            It should not be called directly by the user.
            
        .. TODO::
        
            Add tests.
        
        """
        indices = tuple(sorted((x.index, y.index)))
        # Check if the pairing has already been computed
        try:
            value = self._pairings_dict[indices]
        # If we get a KeyError, the value has not yet been computed.
        except KeyError:
            if not (x.sector + y.sector).is_identity():
                value = 0
            elif x.is_narrow:
                value = 1
            else:
                Wfixg = x.parent_ring.singularity.restrict(x.sector.fixed)
                mr = Wfixg.milnor_ring_ring
                project = mr.cover()
                fg = project(x.monomial * y.monomial)
                hess = project(Wfixg.hessian_det())
        
                # I think something in Sage is buggy - this is to make the
                # pairing work with QQbar. The zero in QQbar says you can't do
                # .lm() on it.
                if fg == 0:
                    value = 0
                elif fg.lm() == hess.lm():
                    value = fg.lc() / hess.lc() * Wfixg.mu
                else:
                    value = 0
            
            # If the result is a rational number, we want to be sure we save
            # it as an object in QQ. Depending on the coefficient
            # ring of the parent, the actual type of the answer may be something
            # else, like Expressions. By making the answers rationals when possible,
            # we allow the pairings dictionary to be used by QuantumRings 
            # with a different coefficient ring.
            try:
                self._pairings_dict[indices] = QQ(value)
            except ValueError:
                # In this case, `value` was not a rational number.
                self._pairings_dict[indices] = value
        return value
 
     
    @staticmethod
    def _inside_doctest():
        """
        Determine whether code is being run by a doctest. This is done by
        looking at the current instance of :class:`SageInteractiveShell`. If
        there is an instance running, then this was called from the shell and
        not a doctest.
        
        .. TODO::
        
            This will return ``True`` if run from the notebook. I don't yet know
            how to do this properly. However, the whole design is probably bad
            and should be redone. --Scott, May 2013
        
        OUTPUT:
        
        - ``True`` if this method was called from inside a doctest; ``False``
          otherwise.
        
        TESTS:
        
        This should pass the doctest, but isn't what you'll get by running this
        function::
            
            sage: QuantumRing._inside_doctest()
            True
        
        AUTHOR:
        
        - Scott Mancuso (June 2012)
        
        """
        shell = sis._instance
        if shell:
            return False
        return True
    
    @staticmethod
    def _inside_timeit():
        """
        Determine whether code is being run by :func:`sage_timeit` (which is
        invoked by ``%timeit``). This is done by looking at ``sys.stdout``. The
        :func:`sage_timeit` redirects ``sys.stdout`` to ``/dev/null``. This
        method checks whether or not this has been done.
        
        When this function evaluates ``True``,
        :meth:`~QuantumRing.QuantumRing._update_products_file`,
        :meth:`~QuantumRing.QuantumRing._update_pairings_file`, and
        :meth:`~FJRW.FJRWRing._update_corrs_file` are disabled and are not
        registered with :mod:`atexit`. This avoids the otherwise many calls to
        those methods that would happen due to the repeated creation of
        :class:`!QuantumRing` s or calls to functions like
        :meth:`~QuantumRing.QuantumRing.products`.
        
        OUTPUT:
        
        - ``True`` if this method was called from inside :func:`sage_timeit`;
          ``False`` otherwise.
            
        TESTS::
        
            sage: from sage.misc.sage_timeit import sage_timeit
            sage: QuantumRing._inside_timeit()
            False
            sage: a = sage_timeit("if not QuantumRing._inside_timeit(): raise "
            ...   "Exception, 'Function broken'", globals())
            sage: a.__module__
            'sage.misc.sage_timeit'
        
        AUTHOR:
        
        - Scott Mancuso (June 2012)
        
        """
        try:
            inside = sys.stdout.name == "/dev/null"
        except AttributeError:
            inside = False
        return inside
    
    
    def _verify_products(self, products_dict=None):
        """
        Check that the currently computed products agree with the values that
        were previously computed and saved. To be run during doctests.
        
        This method checks that the current
        :attr:`~QuantumRing.QuantumRing._products_dict` has no keys that map to
        different values than they did in the version of
        :attr:`~!QuantumRing.QuantumRing._products_dict` that was originally
        loaded by ``self`` during construction.
        
        INPUT:
        
        - ``products_dict`` -- A dictionary of the previously computed products
          for ``self``. Defaults to the dictionary originally loaded from the
          products database.
        
        OUTPUT:
        
        - Raises an :class:`AssertionError` if the items in
          :attr:`self._products_dict <!QuantumRing.QuantumRing._products_dict>`
          don't agree with the items in ``products_dict``. Does not return a
          value.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: H = FJRWRing(SymmetryGroup(QSingularity.create("L23"), "max"),
            ...   print_basis=False)
            sage: H._verify_products()
            sage: H.products()
            H[2] * H[2] = ???
            ...
            H[4] * H[4] = -3/5*H[6]
            sage: H._verify_products()
        
        Make sure that discrepencies are caught.
        
        .. NOTE::
        
            These tests will only pass if you have previously computed all of
            the products mentioned and if you have edited your sage-doctest
            script as explained in the file
            Dropbox/BYU-FJRW-group/report_computation_error_instructions.txt.
        
        ::
            
            sage: H._products_dict[(1, 2)] = H.zero()
            sage: H._products_dict[(1, 3)] = H[2]
            sage: H._verify_products()
            Traceback (most recent call last):
            ...
            AssertionError: The following products failed for FJRW ring for
            x^2*y + x*y^3 with group generated by <(1/5, 3/5)>:
            (1, 2) was {} in self._products_dict but was previously computed as
            {2: 1}.
            (1, 3) was {2: 1} in self._products_dict but was previously computed
            as {3: 1}.
            ******...******
            
        Make sure that if an entry is missing from either dictionary, it doesn't
        cause a failure::
        
            sage: del H._products_dict[(1, 2)]
            sage: del H._products_dict_orig[(1, 3)]
            sage: H._verify_products()
        
        The values we've modified here shouldn't be saved, but fix them just in
        case::
        
            sage: H._products_dict[(1, 2)] = H[2]
            sage: H._products_dict[(1, 3)] = H[3]
            sage: H._products_dict_orig[(1, 3)] = {3: 1}
        
        AUTHOR:
        
        - Scott Mancuso (July 2012)
        
        """
        if products_dict is None:
            try:
                products_dict = self._products_dict_orig
            except AttributeError:
                print("Could not find original _products_dict.")
                return
        
        failed_products = []
        for key, value in self._products_dict.items():
            if key not in products_dict:
                # This product hadn't been computed before, so it can't be
                # wrong.
                continue
            try:
                if isinstance( value, CouldNotComputeException ):
                    assert value == products_dict[key], (
                            "%s was %s in self._products_dict but was "
                            "previously computed as %s."
                            % (key, value, products_dict[key]))
                else:
                    # Check if they have the same `index_data`.
                    assert value._to_dict() == products_dict[key], (
                            "%s was %s in self._products_dict but was "
                            "previously computed as %s."
                            % (key, value._to_dict(), products_dict[key]))
            except (AssertionError, X):
                failed_products.append(X.args[0])
        
        if failed_products:
            raise AssertionError ("The following products failed for %s:\n"
                                   % str(self).rstrip(".")
                                   + "\n".join(failed_products)
                                   + "\n" + "*" * 80)
    
    def _verify_pairings(self, pairings_dict=None):
        """
        Check that the currently computed pairings agree with the values that
        were previously computed and saved. To be run during doctests.
        
        This method checks that the current
        :attr:`~QuantumRing.QuantumRing._pairings_dict` has no keys that map to
        different values than they did in the version of
        :attr:`~!QuantumRing.QuantumRing._pairings_dict` that was originally
        loaded by ``self`` during construction.
        
        INPUT:
        
        - ``pairings_dict`` -- A dictionary of the previously computed pairings
          for ``self``. Defaults to the dictionary originally loaded from the
          pairings database.
        
        OUTPUT:
        
        - Raises :class:`AssertionError` if the items in
          :attr:`self._pairings_dict <!QuantumRing.QuantumRing._pairings_dict>`
          don't agree with the items in ``pairings_dict``. Does not return a
          value.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: H = FJRWRing(SymmetryGroup(QSingularity.create("L32"), "max"),
            ...   print_basis=False)
            sage: H._verify_pairings()
            sage: H.products()
            H[2] * H[2] = ???
            ...
            H[4] * H[4] = -2/5*H[6]
            sage: H._verify_pairings()
        
        Make sure that discrepencies are caught.
        
        .. NOTE::
        
            These tests will only pass if you have previously computed all of
            the pairings mentioned and if you have edited your sage-doctest
            script as explained in the file
            Dropbox/BYU-FJRW-group/report_computation_error_instructions.txt.
        
        ::
            
            sage: H._pairings_dict[(1, 2)] = 1
            sage: H._pairings_dict[(3, 3)] = 0
            sage: H._verify_pairings()
            Traceback (most recent call last):
            ...
            AssertionError: The following pairings failed for FJRW ring for
            x^3*y + x*y^2 with group generated by <(1/5, 2/5)>:
            (1, 2) was 1 in self._pairings_dict but was previously computed as 0.
            (3, 3) was 0 in self._pairings_dict but was previously computed as
            -3/5.
            ******...******
            
        Make sure that if an entry is missing from either dictionary, it doesn't
        cause a failure::
        
            sage: del H._pairings_dict[(1, 2)]
            sage: del H._pairings_dict_orig[(3, 3)]
            sage: H._verify_pairings()
        
        The values we've modified here shouldn't be saved, but fix them just in
        case::
        
            sage: H._pairings_dict[(1, 2)] = 0
            sage: H._pairings_dict[(3, 3)] = -2/5
            sage: H._pairings_dict_orig[(3, 3)] = -2/5
        
        AUTHOR:
        
        - Scott Mancuso (July 2012)
        
        """
        if pairings_dict is None:
            try:
                pairings_dict = self._pairings_dict_orig
            except AttributeError:
                print("Could not find original _pairings_dict.")
                return
        
        failed_pairings = []
        for key, value in self._pairings_dict.items():
            if key not in pairings_dict:
                # This pairing hadn't been computed before, so it can't be
                # wrong.
                continue
            try:
                assert value == pairings_dict[key], (
                        "%s was %s in self._pairings_dict but was previously "
                        "computed as %s." % (key, value, pairings_dict[key]))
            except (AssertionError, X):
                failed_pairings.append(X.args[0])
        
        if failed_pairings:
            raise AssertionError ("The following pairings failed for %s:\n"
                                   % str(self).rstrip(".")
                                   + "\n".join(failed_pairings)
                                   + "\n" + "*" * 80)    
    def __iter__(self):
        """
        Return a generator for this :class:`~QuantumRing.QuantumRing` that will
        loop through all of the elements in :meth:`self.list()
        <QuantumRing.QuantumRing.list>`.
        
        .. TODO::
        
            Add tests.
        
        """
        for b in self.list():
            yield b    
          
    def __getitem__(self, key):
        """
        Provides access to basis elements by their index or by their string name
        using ``[ ]``. The indexes of elements can be seen by using the
        :meth:`~QuantumRing.QuantumRing.print_summary` method. Can also be used
        for slicing. See :class:`FJRW.FJRWRing` and
        :class:`OrbMilnor.OrbMilnorRing` for examples.
        
        .. TODO::
        
            Add tests, especially of slicing.
        
        """
        if key in ZZ:
            if key > 0:
                return self.list()[key - 1]
            elif key < 0:
                return self.list()[key]
            else:
                raise KeyError ("This object is indexed beginning at 1. Use "
                                 "negative numbers to count backwards from the "
                                 "end.")
        
        try:
            return self.basis_by_name[key]
        except TypeError:
            # A slice object was passed in, not a string or integer.
            return self.list()[key.start:key.stop:key.step]

  
    def one(self):
        """
        Return the multiplicative identity of this ring.
        
        """
        #cycle through basis elems and find the one with degree 0
        #this should be the element that comes first - we'll check!
        if self.list()[0].degree == 0:
            return self.list()[0]
        else:
            raise Exception ( "Unexpected ordering of basis - identity should be first!")
    
    def list(self):
        """
        Return a list of the basis elements of this module.
        
        .. TODO::
        
            Add tests.
            
        """
        return list(self.basis())
        
    def _repr_term(self, m):
        """
        Return a string representing the basis element indexed by m.
        Called by the :meth:`~QuantumRing.QuantumRingElement._repr_` method of elements of this ring.
        
        .. TODO::
        
            Add tests.
            
        """
        return repr(m)
        
    def _str_term(self, m): 
        """
        Return a string representing the basis element indexed by m.
        Called by the :meth:`~QuantumRing.QuantumRingElement.__str__` method of elements of this ring.
        
        .. TODO::
        
            Add tests.
        
        """
        return self.prefix() + "[" + str(m) + "]" # mind the (m), to accept a tuple for m
       
    def _latex_term(self, m):
        """
        Return a string for the LaTeX code for the basis element
        indexed by m. Called by the :meth:`~QuantumRing.QuantumRingElement._latex_` method of elements of this ring.
        
        .. TODO::
        
            Add tests.
        
        """
        from sage.misc.latex import latex
    
        return latex(m)

#    _nonprimitive_computed = False
#     def find_nonprimitive(self):
#         """
#         Compute all products in order to determine which classes are not
#         primitive.
#         
#         .. NOTE::
#         
#             Only works for products that are the rational scalar multiple of a
#             basis element.
#         
#         .. TODO::
#         
#             The description doesn't seem to exactly be what this method does, as
#             it doesn't return anything. Should I change the code, or the
#             documentation (and probably the name, which I feel is misleading).
#             
#             I'm thinking I should just incorporate this functionality into the
#             :meth:`~QuantumRing.QuantumRing.products` method and delete this
#             method. Both take about the same amount of time now; I see no reason
#             to have two different methods cycling through all possible products.
#             Would it still be useful to have the warning message printed?
#             
#             On the other hand, this method only runs the first time it's called.
#             That saves substantial time, but doesn't allow for finding more
#             factorizations if more products are found (for example through
#             reconstruction). Should a similar mechanism be added to
#             :meth:`!products`, or should we leave both methods separate, the way
#             they are?
#             
#             (Scott, July 13, 2012)
#         
#         .. TODO::
#         
#             Add tests.
#         
#         """
#         if self._nonprimitive_computed:
#             return
#         self._nonprimitive_computed = True
#         
#         for i, j in Combinations(range(2, len(self.basis) + 1) * 2, 2):
#             try:
#                 a = self[i] * self[j]
#             except CouldNotComputeException:
#                 print("Warning: failed to compute product:  %s * %s."
#                       % (str(self[i]), str(self[j])))
#             if a == 0:
#                 continue
#             if len(a.data) == 1:
#                 a.data.keys()[0].record_factorization(
#                         self[i], self[j],
#                         Rational(1.0 / a.data.values()[0]))
#     
#     @lazy_attr
#     def max_primitive_degree(self):
#         """
#         Return the maximal degree of a primitive class. If the multiplication
#         can not be completely computed, then this is just an upper bound.
#         
#         .. TODO::
#             
#             Needs testing and better doc.
#         
#         """
#         
#         max_deg = 0
#         for h in self:
#             if h.factor() is None and h.degree > max_deg:
#                 max_deg = h.degree
#         return max_deg
#     
    def mirror(self, a, B, verbose=False):
        """
        Find the mirror of the element ``a`` (an element of ``self``) in the
        :class:`~QuantumRing.QuantumRing` ``B``.
        
        INPUT:
        
        - ``a`` -- A :class:`~QuantumRing.BasisElement`.
        - ``B`` -- A :class:`~QuantumRing.QuantumRing`.
        - ``verbose`` -- Set this to ``True`` to get output about possible
          issues with the mirror found. Defaults to ``False``.
        
        OUTPUT:
        
        - A basis element in the :class:`~QuantumRing.QuantumRing` ``B`` if
          there is only one possibility; otherwise a list of all possible
          basis elements that ``a`` could be mapped to.
        
        EXAMPLES::
            
            sage: from LGModels import *
            sage: W = QSingularity.create("C34F6")
            sage: G = SymmetryGroup(W, "J")
            sage: Gt = G.transpose()
            sage: H = FJRWRing(G, print_basis=False)
            sage: B = OrbMilnorRing(Gt, print_basis=False)
            
            sage: e1 = H[8]
            sage: e2 = H[13]
            sage: H.mirror(e1, B)
            b_(1/3, 1/6, 1/2)
            sage: H.mirror(e2, B)
            y^3*z^3b_(0, 0, 0)
        
        .. TODO::
        
            Do we know what to do with noninvertible singularities?
        
        """
        from SymmetryGroup import SymmetryGroupElement, SymmetryGroup
        
        try:
            ats = self.singularity.atomics
        except AttributeError:
            raise ValueError( "This Singularity is not invertible.")
        
        # TODO: atomic types keep track of what they are (loop, fermat, etc.)
        # use this instead of looking at the number of variables.
        Even_Loop = False
        for at in ats:
            if is_even(at.nvariables):
                # We either have a chain or a loop.
                explist = at.polynomial().exponents()
                if all([len(e.nonzero_positions()) == 2 for e in explist]):
                    # Every monomial in this atomic has two variables, so it's
                    # a loop, not a chain.
                    Even_Loop = True
                    break
                        
        if Even_Loop:
            if verbose:
                print ("The Singularity contains an even variable loop. There "
                       "will be multiple possible elements.")
    
        N = self.singularity.nvariables
            
        # Monomial of 'a' gives exponent vector to find group element for 'b'.
        if a.monomial in self.base_ring():
            expon = [0] * N
        else:
            expon = a.monomial.exponents()[0]
            
        # Creates a vector of zeros (outside of fix g) and expon + 1 (in fix g).
        V = []
        fix = a.sector.fixed  # Fixed locus of a.sector.
        for i in range(N):
            if i in fix:
                V.append(expon[i] + 1)
            else:
                V.append(0)
        V = transpose(matrix([V]))
        
        # Multiply by (A^T)^(-1) to get b.g:
        Minv = (transpose(self.singularity.matrix))**-1
        phases = transpose(Minv * V)  # b.g values only.
        GT = self.Gsec.transpose()
        b_g = GT(vector(phases[0]))  # b.g as a group element.
            
        fix = list(b_g.fixed)  # Fixed locus of b.g.
        
        fixlist = []
        for i in range(N):
            if i in fix:
                fixlist.append(1)
            else:
                fixlist.append(0)
        
        # Diagonal matrix w/ones in fixed locus of b.g.
        matrix_fixlist = diagonal_matrix(fixlist)
        
        # 1 x N matrix w/ ones in fixed locus of b.g.
        fixlist = transpose(matrix(fixlist))
        
        # Weird and maybe not efficient way to get all choices for exponents:
        vars = "n0"
        allexp2 = "for n0 in range(0, %s)" % self.singularity.expons[0]
        for i in range(1, N):
            vars += ", n" + str(i)
            allexp2 += ("for n" + str(i) + " in range(0, " +
                        str(self.singularity.expons[i]) + ")")
        allexp = "[(" + vars + ") " + allexp2 + "]"
        # All possible exponent combinations.
        allexp = eval(allexp)
        # Zeros for entries not in fix.
        allexp = [tuple(vector(ae) * matrix_fixlist) for ae in allexp]
        allexp = list(set(allexp))  # Eliminates duplicates.
        G = self.Gsec
        
        # Here we find all choices for monomials that will work.
        mon_exp = []
        for choice in allexp:
            choice = transpose(matrix(choice))
            gptry = self.singularity.matrix.inverse() * (choice + fixlist)
            gptry = vector(QQ,transpose(gptry)[0])
            try:
                gptry = G(gptry)
                if gptry == a.sector:
                    mon_exp.append(list(transpose(choice))[0])
            except TypeError:
                pass
                
        # Takes list of exponents: mon_choice to an actual monomials, b_m.
        mirror_choices = []
        # For every even variable loop, there will be 2x number of elements
        # appended.
        for mon_choice in mon_exp:
            b_m = 1
            for j in range(N):
                b_m *= self.singularity.poly.variable(j)**(mon_choice[j])
            #temp_elem = B._my_basis_element(B, b_m, b_g)
            mirror_choices.append(B.basis()[B._my_basis_element(B, b_m, b_g)])
        
        if len(mirror_choices) == 1:
            return mirror_choices[0]
        else:
            return mirror_choices
    
    def mirror_summary(self, B, verbose=False):
        """
        Print the elements of :attr:`~QuantumRing.QuantumRing.basis` and where
        they map under the mirror map.
        
        INPUT:
        
        - ``B`` -- A :class:`~QuantumRing.QuantumRing`.
        - ``verbose`` -- As in :meth:`~QuantumRing.QuantumRing.mirror`.
        
        Does not return a value.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: W = QSingularity.create("C34F6")
            sage: G = SymmetryGroup(W, "J")
            sage: Gt = G.transpose()
            sage: H = FJRWRing(G, print_basis=False)
            sage: B = OrbMilnorRing(Gt, print_basis=False)
            
            sage: H.mirror_summary(B)
              H[1] ----> B[1]
              H[2] ----> B[2]
              H[3] ----> B[3]
              H[4] ----> B[6]
              H[5] ----> B[7]
            ...
            H[12] ----> B[14]
             H[13] ----> B[10]
             H[14] ----> B[12]
             H[15] ----> B[15]
             H[16] ----> B[16]
            
            sage: B.mirror_summary(H)
              B[1] ----> H[1]
              B[2] ----> H[2]
              B[3] ----> H[3]
              B[4] ----> H[6]
              B[5] ----> H[7]
            ...
             B[12] ----> H[14]
             B[13] ----> H[11]
             B[14] ----> H[12]
             B[15] ----> H[15]
             B[16] ----> H[16]
        
        """
        basis_string_length = max([len(str(a)) for a in self.list()])
        for a in self:
            print(str(a).rjust(basis_string_length + 1), "---->",)
            mirror_choices = self.mirror(a, B, verbose)
            if not isinstance(mirror_choices, (set, list, tuple) ):
                print(mirror_choices)
            else:
                # We got a list instead of a single element.
                print("[%s, %s]" % tuple(mirror_choices))
    

    def _create_elem_from_dict(self, data):
        """
        Return an element of self corresponding to `data`. Used by _compute when loading the products dictionary.
        If data is a CouldNotComputeException, return the exception.
        
        INPUT:
        
        - `data`-- A dictionary whose keys are integers corresponding to the indices of the basis elements of self. The values are the coefficients of the corresponding basis elements.
          Alternatively, this method accepts a CouldNotComputeException as input.
        
        OUTPUT:
        
        - An element of self, or a CouldNotComputeException.
        
        This should be the inverse of the _to_dict method on the elements::
        
            sage: from LGModels import *
            sage: W = QSingularity.create("f52")
            sage: G = SymmetryGroup(W)
            sage: B = OrbMilnorRing(G, print_basis = False)
            sage: a,b,c,d = B.list()
            sage: v = c*c
            sage: B._create_elem_from_dict(v._to_dict()) == v
            True
    
        """
        if data == {}:
            return self.zero()
        else:
            try:
                return sum([self[elem]*data[elem] for elem in data])
            except KeyError:
            # We got a CouldNotComputeException
                return data
        
class CouldNotComputeException(Exception):
    """
    This exception is raised when the code attempts to compute a correlator
    and all implemented methods fail.
    
    """
    def __eq__(self, other):
        return (isinstance(other, CouldNotComputeException)
                and repr(self) == repr(other))


