"""
This module contains:

    SymmetryGroupElement
        Methods:
            is_identity
            in_SL
            log_action
        Attributes:
            value
            fixed
            not_fixed
            index
            good_gens
            
    SymmetryGroup
        Methods:
            list
            subgroup
            is_invariant
            containsJ
            contained_in_SL
            transpose
            find_subgroups
            identity
            gens
            SL_subgroup
        Attributes:
            order
            _Gmax_gens
            poly
            length
AUTHORS:

    - Drew Johnson (2010-2011) Initial design and implementation
    - Rachel Suggs (2011-2012) Object-oriented revision and documentation

"""

try:
    from sage.all import *
except ImportError:
    print("Didn't import Sage!!!")
    
import sys
if "." not in sys.path: sys.path.insert(0,".")

from QSingularity import QSingularity
from Singularity import Singularity
from LazyAttr import lazy_attr
from sage.modules.fg_pid.fgp_module import FGP_Module_class
from sage.modules.fg_pid.fgp_element import FGP_Element
import warnings

def is_SymmetryGroup(x):
    """
    Return true of x is a SymmetryGroup instance.
    
    Called by the :meth:`~!SymmetryGroup.SymmetryGroup.__eq__` method.
    
    EXAMPLES::
    
        sage: from LGModels import *
        sage: W = Qs("F3C24")
        sage: G = Grp(W,"max")
        sage: is_SymmetryGroup(G)
        True
        sage: G1=set(G)
        sage: is_SymmetryGroup(G1)
        False
        
    """
    return isinstance(x, SymmetryGroup)

class SymmetryGroupElement(FGP_Element):
    '''
    Represents an element of a :class:`~SymmetryGroup.SymmetryGroup`.
    
    .. NOTE:: 
        
        Users should not call the constructor directly.  Instead they
        should create an instance of :class:`~SymmetryGroup.SymmetryGroup` and 
        use the :meth:`~SymmetryGroup.get_element` method instead (see documentation below).
    
    CONSTRUCTOR:
    
    - ``parent_group`` -- The :class:`~SymmetryGroup.SymmetryGroup` object to 
      which
      this element belongs.
    - ``numbers`` -- An iterable of rationals representing the phases of the
      action of this group element.  These phases need not be reduced modulo 1.
        
    EXAMPLES::
        
        sage: W = QSingularity.create("L34F7")
        sage: G = SymmetryGroup(W, "max")
        
    Use the :meth:`~SymmetryGroup.get_element` method to retrieve elements to manipulate::
    
        sage: g1 = G.get_element((8/11, 9/11, 5/7))
        sage: g2 = G.get_element((5/11, 7/11, 3/7))
        
    You can use the subscript notation ``[ ]`` to access the phases::
    
        sage: g1[1]
        9/11
        
        sage: g2[2]
        3/7
    
    The group operation is implemented as ``+``::
    
        sage: g1 + g2
        (2/11, 5/11, 1/7)
    
    The :meth:`~SymmetryGroup.SymmetryGroupElement.order` method gives the order
    of the element in the group::
    
        sage: g1.order()
        77
        
    You can treat the group as a left or right `\\mathbb Z` module with
    ``*``::
    
        sage: 11*g1
        (0, 0, 6/7)
        
        sage: g2*3
        (4/11, 10/11, 2/7)
        
    The `sum` method is implemented for symmetry group elements and returns 
    the sum of the phases::
    
        sage: sum(g1)
        174/77
        sage: sum(g2)
        117/77
        
    Group elements can be coerced to `Int`s::
    
        sage: g = G.get_element((0,0,2/7)); print g
        G[55]
        sage: int(g)
        55
    
    The `len` method is also implemented for group elements::
    
        sage: len(g)
        3
        sage: len(g) == len(g1) == len(g2)
        True
    
    The method :meth:`~SymmetryGroup.SymmetryGroupElement.fixed` gives the (0
    based) indices of the fixed locus::
        
        sage: (11*g1).fixed
        set([0, 1])   
        
    Use the :meth:`~SymmetryGroup.SymmetryGroupElement.good_gens` method to get
    the preferred representation of this group element in terms of the preferred
    generators (columns of the inverse exponent matrix)::
        
        sage: alpha = vector(g1.good_gens); alpha
        (2, 0, 5)
        
        sage: W.matrix.inverse() * alpha
        (8/11, -2/11, 5/7)
    
    '''
    def __init__(self, parent_group, numbers):
        """See class documentation for constructor details."""
        super(SymmetryGroupElement, self).__init__(parent_group, numbers)
        
        self.value = tuple( [n-floor(n) for n in self.lift()] )
        """A tuple of rationals representing the phases of the action of this
        group element, reduced modulo 1."""
    
    def is_identity(self):
        """
        Return ``True`` if this element is the identity.
        
        ..NOTE::
        
            This is an alias for the 
            :meth:`~SymmetryGroup.SymmetryGroup.is_zero` method. 
            
        """
        return self.is_zero()

    def sum(self):
        """
        Return the sum of the phases of self. This is also called when the user 
        types sum(SymmetryGroupElement).
        
        ..EXAMPLES::
        
            sage: G = SymmetryGroup(QSingularity.create("L35"), "max")
            sage: id = G[0]; id
            (0, 0)
            sage: sum(id)
            0
            sage: id.sum()
            0
            
            sage: g = G[4]; g
            (2/7, 1/7)
            sage: sum(g)
            3/7
            
        """
        return sum(self.value)

    @lazy_attr
    def fixed(self):
        """
        Return a set of (zero-based) indexes indicating the fixed locus of the
        element.
        
        EXAMPLE::
        
            sage: G = SymmetryGroup(QSingularity.create("L34F7"), "max")
            sage: g = G.get_element((0,0,2/7)); g
            (0, 0, 2/7)
            sage: g.fixed
            set([0, 1])
            
        """
        fixed = [n for n in range(len(self.value)) if self.value[n]==0]
        return set(fixed)

    @lazy_attr    
    def not_fixed(self):    
        """
        Return a set of (zero-based) indexes indicating the complement of the
        fixed locus of the element.
        
        EXAMPLE::

            sage: G = SymmetryGroup(QSingularity.create("L34F7"), "max")
            sage: g = G.get_element((0,0,2/7)); g
            (0, 0, 2/7)
            sage: g.not_fixed
            set([2])
            
        """
        not_fixed = [i for i in range(len(self.value)) if self.value[i] != 0]
        return set(not_fixed)
        
    def __str__(self):
        #return self.parent()._element_string[0] + "[%d]" % self.index
        return str(self.value)
        
    def _repr_(self):
        return str(self.value)
            
    def _hash_(self):
        return hash(self.value)
    
    @lazy_attr
    def index(self):
        """
        Return the index of self in self.parent().list().
        
        EXAMPLES::
        
            sage: G = SymmetryGroup(QSingularity.create("L34F7"), "max")
            sage: g = G.get_element((0,0,2/7)); print g
            G[55]
            sage: g.index
            55
            
        """
        return self.parent().list().index(self)
        
    def __int__(self):
        """
        Return the index of self in self.parent().list().
        
        """
        return self.index
    
    def __len__(self):
        return len(self.value)
    
    def _latex_(self):
        return latex(self.value)
         
    def __getitem__(self, i):
        """
        Return the ``i``th phase of self.
        
        """
        return self.value[i]
     
 
    def in_SL(self):
        """
        Return ``True`` if ``self`` is in `SL_n`, i.e., it has determinant 1.
        
        EXAMPLES::
        
            sage: G = SymmetryGroup(QSingularity.create("F4444"), "max")
            sage: g1 = G.get_element((1/2,1/2,1/4,3/4))
            sage: g2 = G.get_element((1/2,0,0,0))
            sage: g1.in_SL()
            True
            sage: g2.in_SL()
            False
            
        """
        return (sum(self) in ZZ)
     
    def log_action(self, basis_element):
        """
        INPUT:
        
        - ``a`` -- An :class:`~FJRW.FJRWBasisElement`.

        OUTPUT:        
        
        - A rational number in `[0, 1)` representing the logarithm of the action
          of this group element on ``a``.

        EXAMPLES::
            
            sage: from LGModels import *
            sage: W = QSingularity.create("C345")
            sage: G = SymmetryGroup(W,"J")
            sage: F1 = FJRWRing(G)
            FJRW ring for x^3*y + y^4*z + z^5 with group generated by <(1/15, 4/5, 4/5)>.
            Dimension:   20
            Basis:
              [1]  e_(4/15, 1/5, 1/5)   Degree: 0     (0, 0)
              [2]  e_(1/5, 2/5, 2/5)    Degree: 2/3   (1/3, 1/3)
              [3]  e_(3/5, 1/5, 1/5)    Degree: 2/3   (1/3, 1/3)
              [4]  e_(2/15, 3/5, 3/5)   Degree: 4/3   (2/3, 2/3)
              [5]  z^3e_(1/3, 0, 0)     Degree: 4/3   (2/3, 2/3)
              [6]  y*z^2e_(1/3, 0, 0)   Degree: 4/3   (2/3, 2/3)
              [7]  y^2*ze_(1/3, 0, 0)   Degree: 4/3   (2/3, 2/3)
              [8]  y^3e_(1/3, 0, 0)     Degree: 4/3   (2/3, 2/3)
              [9]  e_(8/15, 2/5, 2/5)   Degree: 4/3   (2/3, 2/3)
             [10]  e_(14/15, 1/5, 1/5)  Degree: 4/3   (2/3, 2/3)
             [11]  e_(1/15, 4/5, 4/5)   Degree: 2     (1, 1)
             [12]  e_(7/15, 3/5, 3/5)   Degree: 2     (1, 1)
             [13]  z^3e_(2/3, 0, 0)     Degree: 2     (1, 1)
             [14]  y*z^2e_(2/3, 0, 0)   Degree: 2     (1, 1)
             [15]  y^2*ze_(2/3, 0, 0)   Degree: 2     (1, 1)
             [16]  y^3e_(2/3, 0, 0)     Degree: 2     (1, 1)
             [17]  e_(13/15, 2/5, 2/5)  Degree: 2     (1, 1)
             [18]  e_(2/5, 4/5, 4/5)    Degree: 8/3   (4/3, 4/3)
             [19]  e_(4/5, 3/5, 3/5)    Degree: 8/3   (4/3, 4/3)
             [20]  e_(11/15, 4/5, 4/5)  Degree: 10/3  (5/3, 5/3)
            sage: g1 = G.get_element((1/5,2/5,2/5))
            sage: g2 = G.get_element((4/5,3/5,3/5))
            sage: g1.log_action(F1[9])
            0
            sage: g1.log_action(F1[6])
            2
            sage: g2.log_action(F1[13])
            3
        
        """
        # This first step will cause an exception if the monomial is 1
        try:
            exponents = list(basis_element.monomial.exponents()[0])
        except AttributeError:  
            exponents = [0]*self.parent().length
        # We will add 1 to each coordinate in the fixed locus to account for the 
        # determinant twist.
        for i in basis_element.sector.fixed:
            exponents[i] += 1   
        return sum([x*y for x, y in zip(self.value, exponents)])
    
#     def fixes_poly(self, exp_matrix):
#         """
#         Tell whether or not this group element fixes a polynomial.
#         
#         INPUT:
#            
#         - ``exp_matrix`` -- A matrix encoding the exponents of a polynomial.
#         
#         OUTPUT:
#         
#         - ``True`` if this group element fixes the polynomial represented by
#           ``exp_matrix``.
#           
#         ..TODO: See if anything calls this now that we have a new constructor
#         """
#         
#         action = exp_matrix*matrix(self.value).transpose()
#         return action in ZZ^self.parent.length
#     
    @lazy_attr
    def good_gens(self):
        """
        Return the coefficients of the preferred representation of a group
        element in terms of the columns of the inverse exponent matrix.
           
        OUTPUT:
        
        - A list representing the vector for the special representation of this
          group element in terms of the special generators.  See Krawitz 
          (arXiv:0906.0796v1).
          
        """
        self.parent()._make_look_up()
        return self.parent()._look_up_dict[self]




class SymmetryGroup(FGP_Module_class):
    r"""
    Represents a group of diagonal symmetries for a polynomial.

    CONSTRUCTOR:
    
    - ``poly`` -- The :class:`~Singularity.Singularity` object fixed by this  
      group.  
    - ``generators`` -- A list of generators, written in logarithm form as lists
      of rational numbers.  Defaults to ``None``.  Also accepts some special 
      inputs:
    
        * ``generators = "max"`` -- Creates the maximal symmetry group for this 
          polynomial.
        * ``generators = "J"`` -- Creates the group generated by the exponential     
          grading operator.
        * ``generators = "0"`` or ``0`` or ``None`` -- Creates the trivial 
          group.
        * ``generators = [V, U]`` -- Creates the group isomorphic to V/U, where 
          U and V are ``ZZ``-modules and U is spanned by the columns of the 
          identity matrix of appropriate size. This is used internally by the 
          method :meth:`~SymmetryGroup.SymmetryGroup._module_constructor` and 
          should not be called by the user.

    EXAMPLES:

    First create the singularity `W = x^4y + y^2z + z^3`::
    
        sage: W = QSingularity.create("C423")

    Now construct the :class:`SymmetryGroup` by explicitly specifying the 
    generators::
    
        sage: G = SymmetryGroup(W, [[2/3,1/3,1/3],[3/4,0,0]]); G
        Group of diagonal symmetries for singularity x^4*y + y^2*z + z^3 with 
        generators (1/12, 2/3, 2/3).
        
    In general the constructor raises an exception if the given generators do 
    not fix the polynomial. We demonstrate the various special inputs::
    
        sage: G = SymmetryGroup(W, "max")
        sage: print G
        <(1/24, 5/6, 1/3)>
        
        sage: G = SymmetryGroup(W, "J"); G
        Group of diagonal symmetries for singularity x^4*y + y^2*z + z^3 with 
        generators (1/6, 1/3, 1/3).
        
        sage: G = SymmetryGroup(W); G
        Trivial group of diagonal symmetries for singularity x^4*y + y^2*z + 
        z^3.
        sage: print G
        <(0, 0, 0)>
        
        sage: standard_basis = identity_matrix(2).columns()
        sage: V = span([[1/4,1/2]]+standard_basis, ZZ)
        sage: U = span(standard_basis)
        sage: G = SymmetryGroup(QSingularity.create("F57"), [V,U]); G
        Group of diagonal symmetries for singularity x^5 + y^7 with generators 
        (1/4, 1/2).
        
    Note that the final method of creating a symmetry group does not check that 
    the group actually fixes the given polynomial. For this reason, the user 
    should not construct symmetry groups this way.
        
    Creating a group for a non-invertible singularity works the same way. For 
    example, first create the singularity :math:`W = x^3 + y^3 + z^3 + xyz`::
        
        sage: R.<x, y, z> = QQ[]
        sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
    
    Now construct the :class:`SymmetryGroup`. With :math:`G^{max}`::
    
        sage: G = SymmetryGroup(W, "max")
        sage: print G
        <(0, 1/3, 2/3), (1/3, 0, 2/3)>
        sage: G.list()
        [(0, 0, 0), (1/3, 0, 2/3), (2/3, 0, 1/3), (0, 1/3, 2/3), (1/3, 1/3,
        1/3), (2/3, 1/3, 0), (0, 2/3, 1/3), (1/3, 2/3, 0), (2/3, 2/3, 2/3)]
        
    With an explicit list of generators:: 
    
        sage: G = SymmetryGroup(W, [[1/3, 1/3, 1/3]]); G
        Group of diagonal symmetries for singularity x^3 + x*y*z + y^3 + z^3
        with generators (1/3, 1/3, 1/3).
        
    :class:`SymmetryGroup` instances are also iterable and can use the
    containment operator ``in``.  
    
    Coercion is implemented via the :meth:`~SymmetryGroup.get_element` method for group elements written in logarithmic form as 
    tuples of rationals::
    
        sage: G.get_element((2/3, 2/3, 2/3))
        (2/3, 2/3, 2/3)
        
    In addition, you can access group elements via indexing::
    
        sage: G[2]
        (2/3, 2/3, 2/3)
        
    Comparison operators check containment::
    
        sage: G = SymmetryGroup(W, "max")
        sage: H = G.subgroup([G[1]]); H
        Group of diagonal symmetries for singularity x^3 + x*y*z + y^3 + z^3 
        with generators (1/3, 0, 2/3).
        sage: H < G
        True
        
    The latex method is also implemented for this class::
    
        sage: latex(G)
        \langle \left(0, \frac{1}{3}, \frac{2}{3}\right) , \left(\frac{1}{3}, 0, \frac{2}{3}\right)  \rangle
        sage: G = SymmetryGroup(W); latex(G)
        \langle \left(0, 0, 0\right) \rangle
        
    .. TODO::
    
        Make the constructor check that the group fixes the polynomial when the 
        group is constructed with a pair of modules.
        
    """
    # The class to be used for creating elements of this module.
    Element = SymmetryGroupElement
    
    _element_string = ["G"]
    
    def __init__(self, poly, generators=None):
        """ See class documentation for constructor details. """
        
        self.poly = poly
        """The :class:`~Singularity.Singularity` object that this is supposed to
        be a symmetry group of.  It is not a sage polynomial."""
        try:
            self.length = self.poly.nvariables
            """This is the length of each group element."""
        except AttributeError:
            print("First argument must be a Singularity object")
        
        # `check` indicates whether we still need to verify that the
        # generators are the right length and that they fixt self.poly.
        check = True
        if generators is None or generators == "0" or generators == 0:
            generators = [(0,)*self.length]  #: Generators for this group.
            # If the generators are set by the code, we don't need to check
            # them later.
            check = False
        elif generators == "max":
            generators = self._Gmax_gens
            check = False
        elif generators == "J":
            generators = [tuple(self.poly.q)]
            check = False
            
        # This is the case where the input was not a pair of modules
        if isinstance( generators[0], (tuple, list) ):
            # If the generators were user-inputed, we want to check they are valid
            if check:
                for gen in generators:
                    if len(gen) != self.length:
                        raise ValueError ("The generators are not all the "
                        "right length.")
                    if ( not self.poly.matrix*vector(gen) in     
                         ZZ**len(self.poly.monomials) ):
                        raise ValueError ("The generator %s does not fix the "
                                          "polynomial." % repr(gen))
                                          
            standard_basis = identity_matrix(self.length).columns()
            V = span(generators + standard_basis, ZZ)
            U = V.span(standard_basis)
            
        # This is the case where the input was a pair of modules
        else:
            (V, U) = generators
                
#         else:
#             try:
#                 for gen in generators:
#                     if len(gen) != self.length:
#                         raise ValueError, ("The generators are not all the "
#                         "right length.")
#                     if ( not self.poly.matrix*vector(gen) in     
#                          ZZ**len(self.poly.monomials) ):
#                         raise ValueError, ("The generator %s does not fix the "
#                                           "polynomial." % repr(gen))
#             # If `generators` was a pair of modules, we will get an exception
#             except TypeError:       
#                 (V, U) = generators
#         try:
#             standard_basis = identity_matrix(self.length).columns()
#             V = span(generators + standard_basis, ZZ)
#             U = V.span(standard_basis)
#         # If `generators` was a pair of modules, we will get an exception
#         except AttributeError:
#             pass
            
        super(SymmetryGroup, self).__init__(V,U)
        
   
    #    def __call__(self, argument, check=True):
    def get_element(self, argument):
        """
        Coerce input into an element of this group.
        
        """
        # The parent's call method interperets `argument` the way we want only 
        # when `argument` is a vector.
        if isinstance(argument, (list,tuple)):
            argument = vector(argument) 
        return super(SymmetryGroup, self).__call__(argument)

    def __eq__(self, other):
        """Return True if self and other have the same polynomial and generators.
        
        This method first checks that the polynomials of these groups are the same, 
        and then copies the __eq__ method of FGP_module to check that the groups
        themselves are the same.
        
        """
        if not is_SymmetryGroup(other):
            return False
        if not self.poly == other.poly:
            return False
        return self._V == other._V and self._W == other._W

    def __str__(self):
        if self.gens() != ():
            return "<" + str(list(self.gens()))[1:-1] + ">"
        else:
            return "<" + self.zero().__repr__() + ">"
            
    def _repr_(self):
        if self.gens() != ():
            return ("Group of diagonal symmetries for singularity %s with "
                    "generators %s." % (str(self.poly), 
                    str(list(self.gens()))[1:-1]))
        else:
            return ("Trivial group of diagonal symmetries for singularity %s."
                    % str(self.poly))
    def __hash__(self):
        return hash(self.base_ring())
   
            
    def _latex_(self):
        ltx = r"\langle "
        i = 0
        if self.gens() != ():
            for gen in self.gens():
                if i > 0:
                    ltx += ", "
                ltx += latex(gen) + " "
                i += 1
        else:
            ltx += latex(self.zero())
        ltx += r" \rangle"
        return ltx
        
    @lazy_attr
    def elems(self):
        """
        Return a list of the elements of this group.
        
        .. Note::
            
            You should avoid calling this method, as it creates an extra copy
            of the list of group elements. For cycling through all elements in
            a group, use "for g in SymmetryGroup" instead of "for g in 
            SymmetryGroup.elems" or "for g in SymmetryGroup.list()"
            
        """
        warnings.warn('elems() has been deprecated. To cycle through all elements of a group, use \"for g in SymmetryGroup\".', stacklevel = 3)
        return self._list_from_iterator_cached()
    
    def list(self):
        """
        Return a list of the elements of this group.
        
        .. Note::
            
            For cycling through all elements in a group, use "for g in 
            SymmetryGroup" instead of "for g in SymmetryGroup.list()."
            
        """
        return self._list_from_iterator_cached()
        

    @lazy_attr
    def _Gmax_gens(self):
        """
        Calculates the generators for Gmax via a nifty isomorphism

        ALGORITHM:

        Under the Smith normal form, S = P*A*Q
        -- S is the m x n Smith normal form matrix, with the invariant factors
        on the main diagonal and zeros everywhere else
        -- P is an m x m invertible matrix over ZZ
        -- Q is an n x n invertible matrix over ZZ

        Let Gmax = G1, and let G2 = { h in (QQ/ZZ)^n | S*h in ZZ^m }
        If d1,...,dn are the invariant factors of S, then we have that
        G2 = <(1/d1, 0, ..., 0), ..., (0, ..., 0, 1/dn)>

        Under the map phi(x) = Q^-1 * x, G1 is isomorphic to G2.
        The inverse map phi^-1(x) = Q * x is what we use to calculate
        the generators of Gmax. Multiplying a generator of G2 on the left by Q
        gives us a generator of Gmax.

        OUTPUT:

        List of generators for Gmax. The individual coordinates of each
        generator may not be in [0, 1)

        EXAMPLES:

        ::
            sage: R.<X1,X2,X3,X4,X5> = QQ[]
            sage: W = Singularity.create(X1^3 + X2^3 + X3^3 + X4^3 + X5^3 + X1*X2^2 + X2*X3^2)
            sage: G = SymmetryGroup(W,"max"); G
            Group of diagonal symmetries for singularity X1^3 + X1*X2^2
            + X2^3 + X2*X3^2 + X3^3 + X4^3 + X5^3 with generators
            (0, 0, 0, 0, 1/3), (0, 0, 0, 1/3, 0), (1/3, 1/3, 1/3, 0, 0).
            sage: G._Gmax_gens
            [(0, 0, 0, 0, 1/3), (0, 0, 0, 1/3, 0), (4/3, -2/3, 1/3, 0, 0)]



        AUTHORS:

        - Nathan Cordner (2013)
          - Algorithm design and implementation


        """

        #Consider the exponent matrix as a matrix over the integers
        #The Smith normal form factorization will not work otherwise
        A = self.poly.matrix.change_ring(ZZ)
        m = A.nrows()
        n = A.ncols()

        #Square matrix case: just return columns of the inverse matrix
        if m == n:
            gmax_gens = [tuple(t) for t in A.inverse().columns()]
            return list(gmax_gens)

        #Smith Normal Form factorization -- S = P*A*Q
        S, P, Q = A.smith_form()
        d = S.diagonal() #The numbers on the main diagonal of S
        gmax_gens = []
        standard_basis = identity_matrix(n).columns()

        for i in range(n):
            if d[i] > 1:
                #Computes the ith generator of Gmax
                g_i = (1/d[i]) * Q * standard_basis[i]
                gmax_gens.append(tuple(g_i))

        return list(gmax_gens)



    @lazy_attr
    def _Gmax_gens2(self):
        """
        Return as tuples of rationals the generators of the maximal symmetry 
        group for this singularity.
        
        OUTPUT:

        - A list of tuples corresponding to the generators for the maximal 
          symmetry group.

        
        Note that in general, this will not be a minimal set of generators. In 
        addition, the coordinates of the group elements may not be between zero 
        and one.::
            
            sage: G = SymmetryGroup(QSingularity.create("L222"), "J")
            sage: G._Gmax_gens2
            [(4/9, 1/9, -2/9), (-2/9, 4/9, 1/9), (1/9, -2/9, 4/9)]
            
        Here is another example::    
            
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
            
            sage: G = SymmetryGroup(W, "max"); G.gens()
            ((0, 1/3, 2/3), (1/3, 0, 2/3))
            
            sage: G._Gmax_gens2
            [(1/3, 1/3, 1/3), (1/3, 2/3, 0), (0, 2/3, 1/3), (2/3, 0, 1/3), (2/3,
            1/3, 0), (0, 0, 0), (1/3, 0, 2/3), (2/3, 2/3, 2/3), (0, 1/3, 2/3)]
            
        AUTHORS:
        
            - Drew Johnson (2010-11)
            
                - algorithm design
                
            - Rachel Suggs (2011)
            
                - implementation
                
        """

        # Algorithm:
        #         
        # If the exponent matrix is square, return the columns of its inverse.
        # Otherwise, the maximal group is the intersection of the groups 
        # generated by the columns of all invertible square submatrices of the 
        # exponent matrix. Compute this group as follows:
        # 1. Let `n` be the number of variables in the polynomial fixed by this 
        # group. 
        # 2. Find all possible nxn submatrices of the exponent matrix of the 
        # polynomial and find the first invertible submatrix.
        # 3. For each invertible submatrix (starting from the first invertible
        # submatrix), list all the elements of the group generated by the columns
        # of the inverse of the submatrix.
        # 4. Intersect these lists to find a list of generators of the maximal 
        # group - in fact, this list will contain all the elements of the  
        # maximal group.

        A = self.poly.matrix
        m = A.nrows()
        n = A.ncols()   # Step 1
        
        if m == n:  #square matrix
            gmax_gens = [tuple(t) for t in 
                         A.inverse().columns()]
        else:       #nonsquare matrix
            rows = A.rows()
            
            # Step 2 - Find all possible submatrices.
            # We will check for invertibility as we go.
            possible_submatrices = [matrix([rows[i] for i in t]) for t in 
                                    Combinations(range(0, m), n)]
            
            # find the first invertible submatrix
            count=-1
            for m in possible_submatrices:
                count=count+1
                if m.matrix_over_field().is_invertible():
                    break

            gmax_gens = []
    
            # Step 3
            # List the elements corresponding to the first invertible submatrix
            B = possible_submatrices[count] 
            standard_basis = identity_matrix(n).columns()
            try:
                V = span(B.inverse().columns() + standard_basis, ZZ)
                U = V.span(standard_basis)
                M = V/U  # Mod out by 1 on each factor.
                # Get the elements of M written in rational notation.
                # We need to make sure each coordinate is in [0,1) so the 
                # intersection does what we want
                gmax_gens = set([tuple([i - floor(i) for i in x.lift()]) for x 
                                in list(M)])
            # If the submatrix was noninvertible we get a ZeroDivisionError
            except ZeroDivisionError:
                pass
            
            # Repeat this process on each of the remaining submatrices.
            # After each one, intersect the new list of elements with the old.
            for B in possible_submatrices[count+1:]:
                try:
                    V1 = span(B.inverse().columns() + standard_basis, ZZ)
                    U1 = V1.span(standard_basis)
                    M1 = V1/U1  # Mod out by 1 on each factor.
                    new_values = set([tuple([i - floor(i) for i in x.lift()]) 
                                      for x in list(M1)])
                    # Step 4
                    gmax_gens = gmax_gens.intersection(new_values)
                except ZeroDivisionError:
                    pass
            
        return list(gmax_gens)
        
    def _module_constructor(self, V, W, check=True):
        """
        This overrides a method in the parent FGP_Module class.
        It is used by the :meth:`~SymmetryGroup.SymmetryGroup.subgroup` method.
        
        """
        return SymmetryGroup(self.poly, [V, W]) 

    def subgroup(self, gens):
        """
        Return a :class:`SymmetryGroup` object with the same polynomial as self, 
        spanned by the given generators.
        
        INPUT:
        
        - ``gens`` -- A list of :class:`SymmetryGroupElement` s that are
          contained in this :class:`SymmetryGroup`.
        
        OUTPUT:
        
        - A :class:`SymmetryGroup` that is spanned by the given generators.
        
        .. NOTE::
            
            This is identical to the 
            :meth:`~SymmetryGroup.SymmetryGroup.submodule` method.
        
        EXAMPLES::
        
            sage: G = SymmetryGroup(QSingularity.create("F4444"), "max")
            sage: G.subgroup([G[1]])
            Group of diagonal symmetries for singularity x^4 + y^4 + z^4 + w^4 
            with generators (1/4, 0, 0, 0).
            
        """        
        return self.submodule(gens)
         

    def is_invariant(self, sector, monomial):
        """
        Determine whether a given monomial is invariant in the given sector,
        including the determinant twist.

        INPUT:
        
        - ``sector`` -- A :class:`SymmetryGroupElement` that is the
          sector of origin of the monomial.
        - ``monomial`` -- A Sage polynomial.

        OUTPUT:
        
        - ``True`` if the group acts trivially on the given monomial; ``False``
          otherwise.
        
        .. WARNING::
        
            If a monomial `m` does not appear in a sector `g` the call
            is_invariant( `g`, `m` ) will still return a value, but it will be
            meaningless.
        
        """
        expons = monomial.exponents()[0]
        # Check if each generator `g` fixes the monomial.
        for g in self.gens():   
            action = sum( [(expons[i] + 1)*g[i] for i in sector.fixed] ) 

            # an example would be if expons = (0,0,1)
            # sector = g[0] = (0,0,0), sector.fixed = set([0,1,2])
            # g = Group of diagonal symmetries for singularity x^2 + y^2*z + y*z^2 with generators (1/2, 2/3, 2/3).
            # then expons[0]+1 = 1 and g[0] = (0, 0, 0) 
            # then expons[1]+1 = 1 and g[1] = (1/2, 2/3, 2/3)
            # then expons[2]+1 = 2 and g[2] = (1, 1/3, 1/3)
            # and action = (1/2,1/3,1/3) which is not in ZZ thus is false

            # As soon as any one generator does not fix the monomial, we return 
            # False.
            if not action in ZZ:
                return False
        return True

#     def get_element(self, nums):
#         """
#         Return the :class:`SymmetryGroupElement` corresponding to the tuple
#         ``nums``.
# 
#         INPUT:
#         
#         - ``nums`` -- A tuple of rationals.
# 
#         OUTPUT:
#         
#         - The :class:`SymmetryGroupElement` that is a member of this group
#           corresponding to ``nums``, if one is found.
#         
#         """
#         print ("This method has been deprecated. Use coercion instead (see "
#                "class documentation).")
#         
#         return self(vector(nums))
        
    @lazy_attr
    def order(self):
        """
        Return the order of this :class:`SymmetryGroup` object.
    
        EXAMPLE::
        
            sage: W = QSingularity.create("C234")
            sage: G = SymmetryGroup(W, "J"); G.order
            8
            
        ..NOTE::
        
            This is an alias for the 
            :meth:`~SymmetryGroup.SymmetryGroup.cardinality` method.
            
        """
        return self.cardinality()
        
    def containsJ(self):
        """
        Indicate whether this group contains J; i.e., whether it is admissible 
        for the FJRW construction.
        
        OUTPUT:
        
        Return True if this group contains the exponential grading operator; 
        False otherwise.
        
        Examples::
            sage: G = SymmetryGroup(QSingularity.create("F244"), "max")
            sage: G.containsJ()
            True
            sage: G = SymmetryGroup(QSingularity.create("F244"), "J")
            sage: G.containsJ()
            True
            sage: G = SymmetryGroup(QSingularity.create("F244"), 0)
            sage: G.containsJ()
            False
            
        """
        # If we can coerce J into the group, then it is contained in the group.
        # We will get an error if J was not in the module.
        try:
            J = self.get_element(self.poly.q)
            return True
        except TypeError:   
            return False
         
    def contained_in_SL(self):
        """
        Indicate whether this group is contained in SLn; i.e, whether it is 
        allowed for the B-model construction.
        
        OUTPUT:
        
        Return True if every element of this group has determinant 1; False 
        otherwise.
        
        Examples::
            sage: G = SymmetryGroup(QSingularity.create("F244"), "max")
            sage: G.contained_in_SL()
            False
            sage: G = SymmetryGroup(QSingularity.create("F244"), "J")       
            sage: G.contained_in_SL()
            True
            
        """
        for g in self.gens():
            if not g.in_SL():
                return False
        return True
    
    # A special data structure that stores the expression of group elements in
    # terms of the prefered generators (the columns of the inverse matrix).
    _look_up_dict = None    
    
    def _make_look_up(self):
        """
        Create the ``_look_up_dict`` dictionary, if necessary, for use by the
        :meth:`~SymmetryGroup.SymmetryGroupElement.look_up` method.
        
        This is used (indirectly) by the 
        :meth:`~SymmetryGroup.SymmetryGroup.transpose` method.
        
        """
        # Every element of this group is an integer linear combination of the 
        # columns of Ai, the inverse of the exponent matrix of the polynomial 
        # corresponding to this group. By mirror symmetry, these integers are 
        # the exponents of monomials in a basis of the transpose milnor ring. 
        # From the formulas for these bases, we find that the integers in 
        # question are bounded by the exponents of the polynomial. We try all 
        # such integer linear combinations, and if any one matches a group 
        # element we store this fact in a dictionary.
        
        if self._look_up_dict == None:
            self._look_up_dict = dict()
            Ai = self.poly.matrix.inverse()
            alphas = [(range(expon)) for expon in self.poly.expons]
            for alpha in CartesianProduct(*alphas):
                g = Ai * vector(alpha)
                try:
                    self._look_up_dict[self(g)] = alpha
                # If ``g`` was not an element of this group, we get an error.
                # We don't want to include these elements in the dictionary.
                except TypeError:   
                    pass
                    
    def transpose(self): 
        """
        Return a symmetry group that is the transpose of this group, as defined 
        by Krawitz in arXiv:0906.0796v1.
        
        OUTPUT:
        
        - A :class:`SymmetryGroup` object.
        
        EXAMPLES::
        
            sage: W = QSingularity.create("C234")
            sage: G = SymmetryGroup(W, "J"); G
            Group of diagonal symmetries for singularity x^2*y + y^3*z + z^4
            with generators (1/8, 3/4, 3/4).
        
        We illustrate the fact that the index of :math:`G` in :math:`G^{max}` is 
        equal to the the order of :math:`G^T`::
        
            sage: G.order
            8
            sage: Gt = G.transpose(); Gt.order
            3
            sage: SymmetryGroup(W, "max").order
            24
            
        The double transpose is equal to the original group::
        
            sage: Gt.transpose()
            Group of diagonal symmetries for singularity x^2*y + y^3*z + z^4
            with generators (1/8, 3/4, 3/4).
        
        The transpose of the trivial group is :math:`G^{max}` of the transpose 
        polynomial::

            sage: G = SymmetryGroup(QSingularity.create("F244"), 0)
            sage: Gm = SymmetryGroup(QSingularity.create("F244"), "max")
            sage: Gm == G.transpose()
            True    
            
        """
        WT = self.poly.transpose()
        GmaxT = SymmetryGroup(WT, "max")
        # Good_ones is a list of the elements of the transpose group.
        good_ones = []  
        for g in GmaxT:
            bad = False
            for h in self.gens():
                # This is the condition found in Krawitz. Note that we need only 
                # check this condition for generators of this group.
                if (sum([g[i] * h.good_gens[i] for i in range(len(g.value))])
                    not in ZZ):
                    bad = True
            if not bad:
                good_ones.append(g.value)
        return SymmetryGroup(WT, good_ones)
        
    def find_subgroups(self, eliminate_duplicates=True, in_SLn=False, 
                       contains_J=False):
        """
        Find generators for all subgroups of self.
        
        INPUT:
        
        - ``eliminate_duplicates`` -- Return a list with no duplicate subgroups.
          Defaults to ``True``; set to ``False`` if the method takes too long to
          run.
        - ``in_SLn`` -- Return only those subgroups which are contained in
          `SL_n`. Defaults to ``False``.
        - ``contains_J`` -- Return only those subgroups which contain J.
          Defaults to ``False``.
        
        OUTPUT:
        
        A set of tuples, each of which lists the generators for a subgroup,
        written in rational form
        
        EXAMPLES::
        
            sage: G = SymmetryGroup(QSingularity.create("F333"), "max")
            sage: G.find_subgroups()
            set([((1/3, 1/3, 0),), ((0, 1/3, 1/3),), ((0, 1/3, 1/3), (1/3, 0,
            2/3)), ((1/3, 2/3, 1/3),), ((0, 1/3, 0),), ((0, 1/3, 2/3), (1/3, 0,
            0)), ((0, 1/3, 2/3), (1/3, 0, 2/3)), ((1/3, 2/3, 0),), ((0, 1/3,
            1/3), (1/3, 0, 1/3)), ((0, 1/3, 1/3), (1/3, 0, 0)), ((0, 1/3, 2/3),
            (1/3, 0, 1/3)), ((0, 1/3, 0), (1/3, 0, 0)), ((0, 0, 1/3), (0, 1/3,
            0), (1/3, 0, 0)), ((0, 0, 1/3), (1/3, 0, 0)), ((1/3, 0, 2/3),), ((0,
            1/3, 2/3),), ((0, 0, 1/3), (1/3, 2/3, 0)), ((0, 1/3, 0), (1/3, 0,
            2/3)), ((1/3, 1/3, 1/3),), ((1/3, 0, 1/3),), ((1/3, 1/3, 2/3),),
            ((0, 0, 1/3),), ((0, 0, 1/3), (1/3, 1/3, 0)), ((1/3, 2/3, 2/3),),
            ((0, 0, 1/3), (0, 1/3, 0)), ((0, 1/3, 0), (1/3, 0, 1/3)), ((0, 0,
            0),), ((1/3, 0, 0),)])
            
            sage: G.find_subgroups(in_SLn=True)
            set([((0, 1/3, 2/3),), ((1/3, 0, 2/3),), ((1/3, 1/3, 1/3),), ((0,
            1/3, 2/3), (1/3, 0, 2/3)), ((0, 0, 0),), ((1/3, 2/3, 0),)])
            
            sage: G.find_subgroups(contains_J=True)
            set([((0, 1/3, 1/3), (1/3, 0, 0)), ((1/3, 1/3, 1/3),), ((0, 0, 1/3),
            (1/3, 1/3, 0)), ((0, 0, 1/3), (0, 1/3, 0), (1/3, 0, 0)), ((0, 1/3,
            2/3), (1/3, 0, 2/3)), ((0, 1/3, 0), (1/3, 0, 1/3))])
            
            sage: G.find_subgroups(in_SLn=True,contains_J=True)
            set([((0, 1/3, 2/3), (1/3, 0, 2/3)), ((1/3, 1/3, 1/3),)])
            
            sage: from LGModels import *
            sage: W1 = Qs("C223")
            sage: W2 = Qs("C23F3")
            sage: G1 = Grp(W1,"max")
            sage: G2 = Grp(W2,"max")
            sage: S1 = G1.find_subgroups(contains_J=True)
            sage: S2 = G2.find_subgroups(contains_J=True)
            sage: S1.intersection(S2)
            set([((1/6, 2/3, 2/3),), ((1/3, 1/3, 1/3),)])
            
        Here are some we can check by hand::
        
            sage: G = SymmetryGroup(QSingularity.create("F(24)"), "max")
            sage: G.find_subgroups()
            set([((1/12,),), ((1/2,),), ((1/4,),), ((1/6,),), ((0,),), 
            ((1/8,),), ((1/3,),), ((1/24,),)])    
        
            sage: G.find_subgroups(contains_J=True)
            set([((1/24,),)])
            
            sage: G.find_subgroups(in_SLn=True)
            set([((0,),)])
            
            sage: G.find_subgroups(contains_J=True,in_SLn=True)
            set([])
            
        AUTHORS:
        
            - Rachel Suggs (August 2012)
            
        """
        # Checked by Julian Tay (Oct 2012)
        
        # By the Fundamental Theorem of Finite Abelian Groups, every group we 
        # are interested in is isomorphic to a cross product of cyclic groups of 
        # prime power order. We will first find all cyclic subgroups of self of 
        # prime power order. Then for every divisor of the order of self, we 
        # will find all possible subgroups of this order.
        
        W = self.poly
        # `subgroups` will store (generators of) subgroups in a dictionary 
        # indexed by their order
        # `my_elems` will be a list of possible elements in a subgroup
        subgroups = {} 
        if in_SLn:
            my_elems = [e for e in self if e.in_SL()]
        else:
            my_elems = self._list_from_iterator_cached()
        order = Integer(self.order)
        # `ppc_subgroups` are (generators of) cyclic subgroups of prime power 
        # order, indexed by order
        ppc_subgroups = {}  
        
        # Find cyclic subgroups of prime power order, whose order divides the 
        # order of self. Each of this will be generated by a single element of 
        # the given (prime power) order. Note that `factor` returns a tuple (p, 
        # e) where p is a prime dividing ``order'' and e is its exponent in a 
        # prime factorization of ``order''.
        for (prime, exponent) in order.factor():        
            for i in range(exponent):
                subgroup_order = prime**(i+1)
                elems = copy(my_elems)
                index = 0
                # Look through all the elements for those of the correct order
                while index < len(elems):      
                    g = elems[index]
                    if g.order() == subgroup_order:
                        if g.order() in ppc_subgroups.keys():
                            ppc_subgroups[g.order()].add(g)
                        else:
                            ppc_subgroups[g.order()] = set([g])
                        # Remove other elements that generate the same group to 
                        # minimize duplication
                        rel_prime = [n for n in range(subgroup_order) if 
                                     gcd(n,subgroup_order)==1]
                        for n in rel_prime:
                            elems.remove(g*n)                       
                    else:
                        index += 1

        # Cycle through divisors of the order of self, and for each one, find 
        # all the ways we can make it as a cross product of cyclic groups of 
        # prime power order. This requires us to factor each divisor, and see in 
        # what ways we can combine the factors.
        # We'll add the trivial and maximal groups separately at the end.
        subgroup_orders = order.divisors()[1:-1]    
        # If this group contains J, we want only to look at orders that are 
        # multiples of the orders of J
        if contains_J:     
            J_order = lcm([wt.denominator() for wt in self.poly.q])
            subgroup_orders = [size for size in subgroup_orders if size % 
                               J_order == 0]
        for subgroup_order in subgroup_orders:     
            # Each element of args_to_cart_product corresponds to a prime 
            # dividing subgroup_order. Each element is a list, whose entries are 
            # lists of prime powers such that the product of all the entries is 
            # the largest power of the given prime that divides subgroup_order.
            args_to_cart_product = []       
            for (prime, exponent) in subgroup_order.factor():
                # Partitions(exp) returns a list, each element of which is a 
                # list of integers summing to exp. 
                args_to_cart_product.append([[prime**i for i in part] for part     
                                            in Partitions(exponent)]) 
            subgroups[subgroup_order] = set([])
            for factorization in CartesianProduct(*args_to_cart_product):
                # The next line "flattens" the list ``factorization'' - i.e., 
                # turns a list of lists into a single list
                factorization = [item for sublist in factorization for item in 
                                 sublist] 
                try:
                    # Each entry of new_subgroups_list is a list of generators 
                    # of a subgroup 
                    new_subgroups_list = CartesianProduct(*[ppc_subgroups[o] for 
                                                    o in factorization]).list()
                    new_subgroups_set = set([])
                    for subgroup in new_subgroups_list:
                        # This next step is to eliminate easy duplicates by 
                        # checking that the generators we found are all 
                        # distinct. If the prime factorization was something 
                        # like 3*3, we may have the same generator in each 
                        # coordinate - then this group would be found again when 
                        # we look for groups of order 3.
                        if not len(set(subgroup)) < len(subgroup):  
                            if eliminate_duplicates and not contains_J:
                                # The next two steps put the generators in a 
                                # canonical form to enable elimination of 
                                # duplicates
                                subgroup = SymmetryGroup(W, [g.value for g in     
                                                         subgroup])
                                subgroup = [g.value for g in subgroup.gens()]
                                new_subgroups_set.add(tuple(subgroup))
                            elif eliminate_duplicates and contains_J:
                                subgroup = SymmetryGroup(W, [g.value for g in 
                                                         subgroup])
                                if subgroup.containsJ():
                                    subgroup = [g.value for g in 
                                                subgroup.gens()]
                                    new_subgroups_set.add(tuple(subgroup))
                            else:
                                new_subgroups_set.add(tuple(subgroup))
                    # Note that some groups in subgroups[subgroup_order] may not 
                    # be of the right order. This will occur, for example, in 
                    # the scenario described above with the prime factorization 
                    # 3*3. This does not matter since we return the subgroups in 
                    # one set anyway.
                    subgroups[subgroup_order] = subgroups[subgroup_order].union(
                                                          new_subgroups_set)
                # If there aren't any cyclic subgroups of this prime power 
                # order, we will get an error. We want to skip these bad 
                # subgroup orders.
                except KeyError:    
                    pass           
                        
        # Now we add the trivial group and the whole group, if necessary.
        # We add the trivial group if we do not need our subgroups to contain J.
        # We add the whole group if we don't care whether our subgroups are in 
        # SLn, or if we do care and the whole group is in SLn anyway.
        if not contains_J:
            subgroups[1] = set([(self.identity().value,)])
        if (in_SLn and self.contained_in_SL()) or not in_SLn:
            subgroups[self.order] = set([tuple([gen.value for gen in 
                                         self.gens()])])
            
        # Instead of a dictionary, we return one set of subgroups.    
        return  set([]).union(*[d for d in subgroups.values()]) 
        
    def identity(self):
        """
        Returns the identity element of this group.
        
        EXAMPLES::
        
            sage: W = QSingularity.create("F23")
            sage: G = SymmetryGroup(W, "J")
            sage: G.identity()
            (0, 0)
            
        .. NOTE::
        
            This is an alias for the :meth:`~SymmetryGroup.SymmetryGroup.zero` 
            method.  
            
        """
        
        return self.zero()


    def SL_subgroup(self):
        """
        Returns the subgroup G intersected with SL(n,CC)

        AUTHOR: Nathan Cordner, 2014
        """
        
        SL_gens = []
        for grp_elem in self:
            if grp_elem.in_SL():
                SL_gens.append(list(grp_elem))
        H = SymmetryGroup(self.poly, SL_gens)
        return H
                
