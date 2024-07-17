"""
A module that imports all necessary classes from the code we've written. Use
``from LGModels import *`` to import all of these classes into the global
namespace.

This module also defines several shorthands to save typing::

    Qs = QSingularity.create
    Grp = SymmetryGroup
    Am = FJRWRing
    Bm = OrbMilnorRing

AUTHOR:

-Drew Johnson (2010-2011)

"""
import sys
if not "." in sys.path: sys.path.insert(0,".") 

from FJRW import *
from OrbMilnor import *
from ModuliSpace import *
#from latex_functions import *
from QSingularity import *
from SymmetryGroup import *

# Some shorthands:
Qs = QSingularity.create
Grp = SymmetryGroup
Am = FJRWRing
Bm = OrbMilnorRing

def fjrw(sing_str, names, gens = [], print_basis = True):
    """
    This method creates an FJRW ring using a given singularity and group. It is
    a composite of 3 methods in one:
      - :meth:`QSingularity.QSingularity.create`
      - :meth:`SymmetryGroup.SymmetryGroup.__init__`
      - :meth:`FJRW.FJRWRing.__init__`
    
    INPUT:

        - ``polystring`` -- A string representing the desired polynomial,
          described below.
        - ``names`` -- (optional) The names of the variables, given as a list of
          strings.  You can also pass in a string of one character variable
          names. If you don't specify them, the method will choose x, y, z, and
          w for less that four variables, and X1, ... , XN for N > 4 variables.
        - ``gens`` -- A list of generators, written in logarithm form as lists
          of rational numbers.  Defaults to ``None``.  Also accepts some special
          inputs:
    
          * ``gens = "max"`` -- The maximal symmetry group for this polynomial.
          * ``gens = "J"`` -- The group generated by J
          * ``gens = "0"`` or ``0`` or ``None`` -- The trivial group.
        - ``print_basis`` -- Set this to ``True`` if you want a summary of the state
          space printed immediately after construction. Defaults to ``True``.

    OUTPUT:

        - Gives the FJRW Ring with the singularity and generating group
        - Gives the FJRW Ring
        - Outputs the basis for the FJRW Ring

    EXAMPLES:
    
    The first example is when we do not input the variables::
        
        sage: fjrw("C223", "J")
        FJRW ring for x^2*y + y^2*z + z^3 with group generated by <(1/3, 1/3,
        1/3)>.
        Dimension:   4
        Basis:
        [1]  e_(1/3, 1/3, 1/3)  Degree: 0     (0, 0)
        [2]  e_(0, 0, 0)        Degree: 1     (0, 1)
        [3]  y*z^2e_(0, 0, 0)   Degree: 1     (1, 0)
        [4]  e_(2/3, 2/3, 2/3)  Degree: 2     (1, 1)
        FJRW ring for x^2*y + y^2*z + z^3 with group generated by <(1/3, 1/3,
        1/3)>.
        
    The second example is when we want the variable 'y' and 'z' to be swapped::
    
        sage: fjrw("C223", "xzy", "J", print_basis=False)
        FJRW ring for x^2*z + z^2*y + y^3 with group generated by <(1/3, 1/3,
        1/3)>.
        
    """
    
    # This allows for there not to be a names input. If the user does not input
    # a variable, then the function will redefine 'gens' to be the second 
    # variable.
    if gens == []:
        gens = names
        names = []
    W = Qs(sing_str, names)
    G = Grp(W, gens)
    return Am(G, print_basis=print_basis)
    
def om(sing_str, gens, print_basis):
    W = Qs(sing_str)
    G = Grp(W, gens)
    return Bm(G, print_basis=print_basis)


def construct_from_db_filename(file_safe_repr):
    """
    Create a :class:`~QuantumRing.QuantumRing` from the filename used to save
    its products and other computations in the database, i.e.\ the string
    returned by :meth:`~QuantumRing.QuantumRing._file_safe_repr`. Also check
    that the new instance has the same
    :meth:`~!QuantumRing.QuantumRing._file_safe_repr` as the original. If
    not, an :exc:`AssertionError` is raised.
    
    INPUT:
    
    - ``file_safe_repr`` -- A string representing a
      :class:`~QuantumRing.QuantumRing`, in the form returned by
      :meth:`~QuantumRing.QuantumRing._file_safe_repr`. If a filename is passed
      in, the extension and all containing directories are stripped before the
      name is processed.
    
    OUTPUT:
    
    - A new :class:`~QuantumRing.QuantumRing` instance.
    
    EXAMPLES::
    
        sage: from LGModels import *
        sage: W = QSingularity.create("L33C26")
        sage: G = SymmetryGroup(W, "J")
        sage: Gt = G.transpose()
        sage: H = FJRWRing(G, print_basis=False)
        sage: B = OrbMilnorRing(Gt, print_basis=False)
        
        sage: H_rep = H._file_safe_repr(); H_rep
        'FJRW_ring_X1^3*X2_+_X1*X2^3_+_X3^2*X4_+_X4^6_<(3_4,_3_4,_11_12,_1_6)>'
        sage: B_rep = B._file_safe_repr(); B_rep
        'Orbifold_Milnor_ring_X1^3*X2_+_X1*X2^3_+_X3^2_+_X3*X4^6_<(1_8,_5_8,_1_2,_3_4)>'
        sage: H_bar = construct_from_db_filename(H_rep); H_bar
        FJRW ring for X1^3*X2 + X1*X2^3 + X3^2*X4 + X4^6 with group generated by
        <(3/4, 3/4, 11/12, 1/6)>.
        sage: B_bar = construct_from_db_filename(B_rep); B_bar
        Orbifold Milnor ring for X1^3*X2 + X1*X2^3 + X3^2 + X3*X4^6 with
        group generated by <(1/8, 5/8, 1/2, 3/4)>.
        sage: H._file_safe_repr() == H_bar._file_safe_repr()
        True
        sage: B._file_safe_repr() == B_bar._file_safe_repr()
        True
    
    Rings with an explicitly defined :attr:`~QuantumRing.QuantumRing.Ginv`
    are handled correctly::
        
        sage: G_max = SymmetryGroup(W, "max")
        sage: H = FJRWRing(G_max, G, print_basis=False); H
        FJRW ring for x^3*y + x*y^3 + z^2*w + w^6 with group generated by 
        <(1/4, 1/4, 1/4, 1/2), (7/8, 3/8, 11/12, 1/6)> but with invariants 
        taken with the group generated by G' = <(3/4, 3/4, 11/12, 1/6)>.
        sage: H_rep = H._file_safe_repr(); H_rep
        'FJRW_ring_X1^3*X2_+_X1*X2^3_+_X3^2*X4_+_X4^6_<(1_4,_1_4,_1_4,_1_2),_(7_8,_3_8,_11_12,_1_6)>_<(3_4,_3_4,_11_12,_1_6)>'
        sage: H_bar = construct_from_db_filename(H_rep); H_bar
        FJRW ring for X1^3*X2 + X1*X2^3 + X3^2*X4 + X4^6 with group
        generated by <(1/4, 1/4, 1/4, 1/2), (7/8, 3/8, 11/12, 1/6)> but with
        invariants taken with the group generated by G' = <(3/4, 3/4, 11/12,
        1/6)>.
        sage: H._file_safe_repr() == H_bar._file_safe_repr()
        True
    
    The trivial group is handled correctly::
    
        sage: G0 = G_max.transpose()
        sage: B = OrbMilnorRing(G0, print_basis=False); B
        Orbifold Milnor ring for x^3*y + x*y^3 + z^2 + z*w^6 with group generated by <(0, 0, 0, 0)>.
        sage: B_rep = B._file_safe_repr(); B_rep
        'Orbifold_Milnor_ring_X1^3*X2_+_X1*X2^3_+_X3^2_+_X3*X4^6_<(0,_0,_0,_0)>'
        sage: B_bar = construct_from_db_filename(B_rep); B_bar
        Orbifold Milnor ring for X1^3*X2 + X1*X2^3 + X3^2 + X3*X4^6 with group generated by <(0, 0, 0, 0)>.
        sage: B._file_safe_repr() == B_bar._file_safe_repr()
        True
    
    Rings created with :class:`~Singularity.Singularity`\ s are handled
    correctly::
        
        sage: R.<x, y, z> = QQ[]
        sage: W = Singularity.create(x^2*y + y^2*z + z^2*x + x*y*z)
        sage: G = Grp(W, "J")
        sage: H = Am(G, print_basis=False); H
        FJRW ring for x^2*y + x*y*z + x*z^2 + y^2*z with group generated by 
        <(1/3, 1/3, 1/3)>.
        sage: H_rep = H._file_safe_repr(); H_rep
        'FJRW_ring_X1^2*X2_+_X1*X2*X3_+_X1*X3^2_+_X2^2*X3_<(1_3,_1_3,_1_3)>'
        sage: H_bar = construct_from_db_filename(H_rep); H_bar
        FJRW ring for X1^2*X2 + X1*X2*X3 + X1*X3^2 + X2^2*X3 with group
        generated by <(1/3, 1/3, 1/3)>.
        sage: H._file_safe_repr() == H_bar._file_safe_repr()
        True
    
    """
    # Strip all directories and extensions.
    file_safe_repr = os.path.basename(os.path.splitext(file_safe_repr)[0])
    
    # Save the original string for comparison at end.
    ring_str = file_safe_repr
    
    # Split the string into its component parts.
    ring_type_str, ring_str = ring_str.split("ring_", 1)
    poly_str, ring_str = ring_str.split("_<", 1)
    gsec_str, ring_str = ring_str.split(">", 1)
    
    # Format each part for use in the cohomology code.
    ring_type = FJRWRing if ring_type_str.startswith("FJRW") else OrbMilnorRing
    poly_str = poly_str.replace("_", " ")
    # Need to make the generators be a list of lists.
    gsec_str = "[%s]" % gsec_str.replace(",_", ", ").replace("_", "/")
    gsec_gens = sage_eval(gsec_str)
    
    # Try to make a `QSingularity`, but if it fails make a `Singularity`.
    try:
        W = Qs(poly_str, show_parse=False)
    except:
        var_count = 1
        var_names = []
        while True:
            var_name = "X%d" % var_count
            if var_name in poly_str:
                var_names.append(var_name)
                var_count += 1
            else:
                break
        R = PolynomialRing(QQ, var_names)
        poly = R(poly_str)
        W = Singularity.create(poly)
    
    Gsec = Grp(W, gsec_gens)
    # Check for an explicit Ginv.
    if "<" in ring_str:
        # The only things left in ring_str should be the generators for Ginv,
        # and the string should have the form '_<gens>'.
        ginv_str = ring_str.replace("_<", "[").replace(">", "]")
        ginv_str = ginv_str.replace(",_", ", ").replace("_", "/")
        ginv_gens = sage_eval(ginv_str)
        Ginv = Grp(W, ginv_gens)
    else:
        Ginv = "default"
    
    # Create the desired `QuantumRing`.
    Q = ring_type(Gsec, Ginv, print_basis=False)
    assert Q._file_safe_repr() == file_safe_repr, ("original ring was %s but "
                                                   "the ring created was %s" 
                                                   % (file_safe_repr, 
                                                      Q._file_safe_repr()))
    return Q
