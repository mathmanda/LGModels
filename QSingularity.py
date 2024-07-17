"""
.. TODO::

    Document this module.
    
"""
# if not __name__ == '__main__':  # i.e. if this is being imported rather than 
                                # read as a load or attach.
try:
    from sage.all import *
except ImportError:
    print("Didn't import Sage!!!")

import sys
if "." not in sys.path: sys.path.insert(0,".")

from Singularity import Singularity, SingularityError
from LazyAttr import lazy_attr


class PolyType(SageObject):
    """An enum representing the types of quasihomogeneous polynomials."""
    
    Fermat = 0
    Loop = 1
    Chain = 2
    Empty = 3
    RChain = 4
    RLoop = 5

    @classmethod
    def transpose(cls, ptype):
        if ptype == cls.Fermat:
            return cls.Fermat
        if ptype == cls.Loop:
            return cls.RLoop
        if ptype == cls.Chain:
            return cls.RChain
        if ptype == cls.RChain:
            return cls.Chain
        if ptype == cls.RLoop:
            return cls.Loop


class AtomicPolyType(SageObject):
    """
    Represents an atomic polynomial as type with exponents, without named
    variables.
    
    """
    
    def __init__(self, t, e):
        self.type = t
        self.expon = e
        self.nvariables = len(e)

    def expons_of_milnor_ring(self):
        """
        Returns a list of lists containing the exponents of monomials that
        generate the Milnor ring.
        
        """
        
        if self.type == PolyType.Fermat:
            return [[i] for i in range(0, self.expon[0] - 1)]
        
        lll= [range(self.expon[i]) for i in 
                                range(len(self.expon))]
        #print(lll)

        mr = cartesian_product(lll)
        
        if self.type == PolyType.Loop or self.type == PolyType.RLoop:
            return mr

        def delta_even(number):
            if number % 2 == 0:
                return 1
            else:
                return 0

        the_good_ones = []

        if self.type == PolyType.Chain:
            for m in mr:
                j = 0
                while j < len(self.expon) and (m[j] == delta_even(j) * 
                                               (self.expon[j] - 1)):
                    j += 1
                longest_special = j
                if longest_special % 2 == 0:
                    the_good_ones.append(m)

        elif self.type == PolyType.RChain:
            n = len(self.expon)
            for m in mr:
                j = n - 1
                while j >= 0 and m[j] == delta_even(j + n + 1)*(self.expon[j] - 1):
                    j -= 1
                longest_special = n - j - 1
                if longest_special % 2 == 0:
                    the_good_ones.append(m)
        else:
            raise QSingularityError( "Passed in bad type?")

        return the_good_ones
        
    def str(self):
        """Returns the string representation of this AtomicPolyType."""
        if self.type == PolyType.Fermat :
            return "F(" + ", ".join(map(str, self.expon)) + ")"
        elif self.type == PolyType.Chain :
            return "C(" + ", ".join(map(str, self.expon)) + ")"
        elif self.type == PolyType.Loop :
            return "L(" + ", ".join(map(str, self.expon)) + ")" 
        elif self.type == PolyType.RChain :
            return "RC(" + ", ".join(map(str, self.expon)) + ")"
        elif self.type == PolyType.RLoop :
            return "RL(" + ", ".join(map(str, self.expon)) + ")"
    
    def transpose(self):
        return AtomicPolyType(PolyType.transpose(self.type), self.expon)


class AtomicPoly(SageObject):
    def __init__(self, atomicPolyType, vars):
        self.expType = atomicPolyType
        if len(vars) != self.expType.nvariables:
            raise QSingularityError ( "Number of variables does not match type")
        self.vars = vars
        self.nvariables = atomicPolyType.nvariables

    @staticmethod
    def empty():
        """
        Returns the empty :class:`AtomicPoly`.
        """
        
        return AtomicPoly(AtomicPolyType(PolyType.Empty, []), [])

    def milnor_ring(self):
        return self.make_monomials(self.expType.expons_of_milnor_ring())

    def make_monomials(self, exponList, cur_var_index=0):
        """
        INPUT:
        
        - ``exponList`` -- A list of lists storing the exponents of some
          monomials.
        - ``cur_var_index`` -- An index that shows which variables of R to use.
        
        OUTPUT:
        
        - A list of monomials in the appropriate variables.
        """
        
        monoms = []
        for m in exponList:
            i = 0
            mv = 1
            for e in m:
                mv *= self.vars[i + cur_var_index] ** e
                i += 1
            monoms.append(mv)
        return monoms

    def polynomial(self):
        W = 0
        if self.expType.type == PolyType.Fermat:
                W += self.vars[0]**self.expType.expon[0]
        elif self.expType.type == PolyType.Loop:
            current_var_index = 0
            for e in self.expType.expon[:-1]:
                W += (self.vars[current_var_index]**e * 
                      self.vars[current_var_index + 1])
                current_var_index += 1
            W += (self.vars[current_var_index]**self.expType.expon[-1] * 
                  self.vars[0])
        elif self.expType.type == PolyType.Chain:
            current_var_index = 0
            for e in self.expType.expon[:-1]:
                W += (self.vars[current_var_index]**e *
                      self.vars[current_var_index + 1])
                current_var_index += 1
            W += (self.vars[current_var_index] ** 
                  self.expType.expon[current_var_index])
        elif self.expType.type == PolyType.RLoop:
            current_var_index = 0
            for e in self.expType.expon:
                W += (self.vars[current_var_index]**e * 
                      self.vars[current_var_index - 1])
                current_var_index += 1
        elif self.expType.type == PolyType.RChain:
            current_var_index = 1
            W += self.vars[0]**self.expType.expon[0]
            for e in self.expType.expon[1:]:
                W += (self.vars[current_var_index]**e * 
                      self.vars[current_var_index - 1])
                current_var_index += 1

        return W

    def restrict(self, fixed):
        """
        INPUT:
        
        - ``fixed``-- A list of indexes of the fixed locus, i.e. the variables 
          to be preserved.  The indexes should be zero based.
        """
        fixed = sorted(fixed)
        if fixed == []:
            return AtomicPoly.empty()
        if fixed == range(0, self.nvariables):
            return self

        if self.expType.type == PolyType.Fermat:
            #raise QSingularityError ("Bad input to restrict in AtomicPoly "
            #                          "class for Fermat! %(fixed)s" % locals())
            return AtomicPoly(AtomicPolyType(self.expType.type, 
                                             self.expType.expon[fixed[0]:]), 
                              self.vars[fixed[0]:])
        elif self.expType.type == PolyType.Chain:
            if fixed[0] + len(fixed) != self.nvariables:
                raise QSingularityError ("Bad input to restrict in AtomicPoly "
                                          "class for Chain!" + str(fixed))
            if len(fixed) == 1:  # It becomes a Fermat.
                return AtomicPoly(AtomicPolyType(
                                            PolyType.Fermat, 
                                            [self.expType.expon[fixed[0]]]), 
                                  [self.vars[fixed[0]]])
            return AtomicPoly(AtomicPolyType(self.expType.type, 
                                             self.expType.expon[fixed[0]:]), 
                              self.vars[fixed[0]:])
        elif self.expType.type == PolyType.RChain:
            if fixed[-1] + 1 != len(fixed):
                raise QSingularityError ("Bad input to restrict in AtomicPoly "
                                          "class for RChain!" + str(fixed))
            if len(fixed) == 1:  # It becomes a Fermat.
                return AtomicPoly(AtomicPolyType(
                                            PolyType.Fermat, 
                                            [self.expType.expon[fixed[-1]]]), 
                                  [self.vars[fixed[-1]]])
            return AtomicPoly(AtomicPolyType(
                                        self.expType.type, 
                                        self.expType.expon[:(fixed[-1] + 1)]), 
                              self.vars[:(fixed[-1] + 1)])
        elif (self.expType.type == PolyType.Loop or 
              self.expType.type == PolyType.RLoop):
            if len(fixed) != self.nvariables:
                raise QSingularityError ("Bad input to restrict in AtomicPoly "
                                          "class for Loop!" + str(fixed))
            else:
                return self
        # If we didn't do any of those cases...
        raise QSingularityError ("Bad input to restrict in AtomicPoly class! "
                                  "(no case caught it)" + str(fixed))

    def transpose(self, newvars):
        return AtomicPoly(self.expType.transpose(), newvars)
        
    @lazy_attr
    def str(self):
        """
        Returns the string representation of this AtomicPoly.
        """
        return self.expType.str()


class QSingularity(Singularity):
    """
    A class representing a quasihomogeneous polynomial as a sum of atomic types,
    as well as a ring that it lives in.

    See the :meth:`~QSingularity.create` method for examples.
    """
    
    def __init__(self, atomicPolys, polystring = ""):
        """
        .. NOTE:: 
            
            Not recommended for use by users.  Use the 
            :meth:`~QSingularity.create` method instead.
            
        """
        
        # Create poly.
        self.atomics = atomicPolys
        poly = 0
        for atomic in self.atomics:
            poly += atomic.polynomial()

        self.poly = poly
        """The polynomial representing this :class:`~QSingularity.QSingularity`.
        Should be a sage polynomial."""
        self.polystring = polystring
        try:
            self.ring = poly.parent()
            """The :class:`PolynomialRing` that :attr:`self.poly
            <QSingularity.QSingularity.poly>` lives in."""
        except AttributeError:
            # This should only happen if we're making the empty QSingularity.
            self.ring = None

    def is_zero(self):
        return self.atomics == []

    @classmethod
    def from_types_and_ring(cls, atomicTypes, R, var_names):
        """
        Factory method.  Construct with a list of 
        :class:`~QSingularity.AtomicPolyType` objects in the polynomial ring 
        ``R``.
        
        .. NOTE::
        
            Not recommended for use by users.  Use the 
            :meth:`~QSingularity.create` method instead.
        
        INPUT:
        
        - ``var_names`` -- A list of the variables in R in the order
          corresponding to the given ``atomicTypes``. If ``None``, the default
          order of ``R`` is used.
        
        """
        # If the given variables aren't in R, use the ones that are instead.
        if not var_names or not set(var_names) <= set(R.gens()):
            var_names = R.gens()
        
        if sum([len(atomic.expon) for atomic in atomicTypes]) > len(var_names):
            raise QSingularityError( "Not enough vars in polynomial ring!")
        atomics = []
        curIndex = 0
        for atype in atomicTypes:
            atomics.append(AtomicPoly(atype, [var_names[i] for i in range(
                                      curIndex, curIndex + atype.nvariables)]))
            curIndex += atype.nvariables
        return cls(atomics)

    @classmethod
    def create(cls, polystring, names=[], coefficient_ring=QQ, 
               show_parse=True, var_order="xyzw"):
        """
        Factory method. The preferred way to construct this object.
        
        INPUT:
        
        - ``polystring`` -- A string representing the desired polynomial,
          described below.
        - ``names`` -- (optional) The names of the variables, given as a list
          of strings.  You can also pass in a string of one character
          variable names.  If you don't specify them, the method will
          choose ``x``, ``y``, ``z``, and ``w`` for less that four
          variables, and ``X1, ... , XN`` for N > 4 variables.
        - ``coefficient_ring`` -- (optional) The coefficient ring of the
          polynomial. Should be a field. Defaults to the rationals.
        - ``show_parse`` -- A boolean to be passed to
          :meth:`~QSingularity.QSingularity.icreate` to say whether a summary of
          the polynomial should be printed after it has been parsed. Defaults to
          ``True``.
        - ``var_order`` -- The names of the variables, given in the same format
          as ``names``, but in the order that they should appear in the
          polynomial ring that the polynomial will live in. See examples below.
          There are three different possible default values:
        
          #. ``"xyzw"`` if the variables in the polynomial are x, y, z, and w.
          #. ``names`` if ``names`` is given explicitly and the first form of 
             ``polystring`` (described below) is used.
          #. alphabetical order if the second form of ``polystring`` (i.e. a 
             polynomial) is used.
        
        OUTPUT:

        - A :class:`QSingularity` object.

        The input ``polystring`` uses the characters ``F``, ``L``, and ``C`` to 
        represent Fermat, loop, and chain types, respectively.  (Lowercase 
        letters may also be used, but uppercase is preferred because l looks 
        like 1.) Each such letter should be followed by a list of exponents.  
        You can create several Fermats at once, for example ``"F456"`` is the 
        same as ``"F4F5F6"``.  All spaces in ``polystring`` are removed before 
        being processed.
        
        To create a polynomial with exponents larger than 9, enclose each 
        exponent that has multiple digits in a set of parentheses.  For example,
        ``"F456"`` creates a Fermat with three terms having exponents 4, 5, and 
        6. ``"F(45)6"`` creates a Fermat with two terms having exponents 45 and 
        6.
        
        It is also possible to create a :class:`QSingularity` object by passing
        in the actual polynomial that represents the singularity. The
        :meth:`~QSingularity.create` method will then parse the polynomial and
        determine how it breaks into atomic parts. In this case, the
        :meth:`~QSingularity.create` method then prints the polystring for the
        singularity, as well as the order of the variables.

        Prepending either ``L`` or ``C`` with ``R`` (or ``r``) creates a 
        "reverse" chain or loop-- one with the pointers going backwards.

        EXAMPLES::
            
            sage: QSingularity.create("F45")
            Singularity defined by polynomial x^4 + y^5.

            sage: QSingularity.create("L678", "abc")
            Singularity defined by polynomial a^6*b + a*c^8 + b^7*c.

            sage: QSingularity.create("C555L777F888")
            Singularity defined by polynomial X1^5*X2 + X2^5*X3 + X3^5 + X4^7*X5
            + X4*X6^7 + X5^7*X6 + X7^8 + X8^8 + X9^8.

            sage: QSingularity.create("x454L98")
            Traceback (most recent call last):
                ...
            QSingularityError: Invalid input string. See documentation for 
            instructions and examples.

            sage: QSingularity.create("L23L56", ["xhat", "yhat", "zbar", 
            ...   "wbar"])
            Singularity defined by polynomial xhat^2*yhat + xhat*yhat^3 + 
            zbar^5*wbar + zbar*wbar^6.

        Notice that for a reverse loop, ``X1`` points to ``X5`` instead of
        ``X2``::
        
            sage: QSingularity.create("RL88888")
            Singularity defined by polynomial X1^8*X5 + X1*X2^8 + X2*X3^8 + 
            X3*X4^8 + X4*X5^8.

        Notice the difference between a chain and a "reverse" chain::
        
            sage: QSingularity.create("C996")
            Singularity defined by polynomial x^9*y + y^9*z + z^6.

            sage: QSingularity.create("RC996")
            Singularity defined by polynomial x^9 + x*y^9 + y*z^6.
            
        Some examples with large exponents::

            sage: QSingularity.create("F23(23)4")
            Singularity defined by polynomial x^2 + y^3 + z^23 + w^4.

            sage: QSingularity.create("C(45)67l32(32)c99(999)")
            Singularity defined by polynomial X1^45*X2 + X2^6*X3 + X3^7 + 
            X4^3*X5 + X4*X6^32 + X5^2*X6 + X7^9*X8 + X8^9*X9 + X9^999.

            sage: QSingularity.create("Rl234F(23)4RC2(34)", "abcdefg")
            Singularity defined by polynomial a^2*c + a*b^3 + b*c^4 + d^23 + e^4
            + f^2 + f*g^34.
        
        Some examples passing in a polynomial::
            
            sage: QSingularity.create("x^11 + x*w^2 + y^4*z + y*z^3")
            C2(11)L43
            [w, x, y, z]
            Singularity defined by polynomial x^11 + x*w^2 + y^4*z + y*z^3.
            
            sage: QSingularity.create("xhat^3*yhat + yhat^4*xhat + zhat^5")
            F5L43
            [zhat, yhat, xhat]
            Singularity defined by polynomial xhat^3*yhat + xhat*yhat^4 + 
            zhat^5.
            
            sage: QSingularity.create("x^8*z^1 + x^1*w^2 + y^3*w^1 + y^1*z^3")
            L8332
            [x, z, y, w]
            Singularity defined by polynomial x^8*z + x*w^2 + y^3*w + y*z^3.
        
        Explicitly defining the order that the variables appear in the
        polynomial ring:
        
        This first example shows how to make a
        :class:`~!QSingularity.QSingularity` where the first variable points to
        the third, while the second is a Fermat::
        
            sage: W = QSingularity.create("C23F5", "xzy", var_order="xyz"); W
            Singularity defined by polynomial x^2*z + y^5 + z^3.
            sage: W.ring
            Multivariate Polynomial Ring in x, y, z over Rational Field
            sage: W.vars
            [x, y, z]
        
        Easily intertwine a loop and a chain::
        
            sage: W = QSingularity.create("C345L678", ["X1", "X3", "X5", "X2",
            ...   "X4", "X6"], var_order=["X1", "X2", "X3", "X4", "X5", "X6"])
            sage: W
            Singularity defined by polynomial X1^3*X3 + X2^6*X4 + X2*X6^8 +
            X3^4*X5 + X4^7*X6 + X5^5.
            sage: W.ring
            Multivariate Polynomial Ring in X1, X2, X3, X4, X5, X6 over Rational
            Field
        
        Control the order in which a polynomial is parsed::
        
            sage: W = QSingularity.create("a^2 + b^5*e + e^3 + c^3*a + d^6", 
            ...   var_order="abcde", show_parse=False); W
            Singularity defined by polynomial a^2 + a*c^3 + b^5*e + d^6 + e^3.
            sage: W.vars
            [a, b, c, d, e]
            sage: W.q
            (1/2, 2/15, 1/6, 1/6, 1/3)
            
        Some examples with user-defined coefficient rings::
        
        .. skip::
        
        .. TODO::
            
            Add tests here.
        
        """
        
        if not coefficient_ring.is_field():
            raise TypeError( "Input variable coefficient_ring must be a field")
        
        # Remove all whitespace.
        polystring = polystring.replace(" ", "")
        
        import re
        if re.search(r"\^", polystring, False):
            polystring, names = cls.icreate(polystring, show_parse)
            # If the variables were found by parsing and no explicit order was
            # given, we want to put them in alphabetical order.
            if var_order is None or set(names) != set(var_order):
                var_order = sorted(names)
        
        # Make all letters uppercase.
        polystring = polystring.upper()
        # Verify that polystring has the right form and no erroneous characters.
        validate_r = re.compile(r"(([rR]?[flcFLC])((\d+)|\(\d+\))+)+")
        poly_match = validate_r.match(polystring)
        try:
            if poly_match.end() != len(polystring):
                raise ValueError
        except (AttributeError, ValueError):
            raise QSingularityError ("Invalid input string. See documentation "
                                      "for instructions and examples.")
        
        # Verify that there are no inadmissible exponents.
        bad_exponents = re.search(r"[flcFLC](\d+|\(\d+\))*?(0|1)|\((0*1?)\)", 
                                  polystring)
        if bad_exponents:
            raise QSingularityError ("Invalid input string. One or more "
                                      "variables have an inadmissible exponent "
                                      "of %s." 
                                      % int(max(bad_exponents.groups())))
        
        # Start parsing polystring to construct the singularity.
        r = re.compile(r"([rR]?[flcFLC])([^rflcRFLC]+)")
        type_strings = r.findall(polystring)
        type_objects = []
        tot_vars = 0
        
        for polytype in type_strings:
            # This next section is used to determine which exponents have
            # multiple digits and which don't.
            l = re.compile(r"\(")
            r = re.compile(r"\)")
            # Use 'o' as a delimiter to mark large exponents.
            polytype1 = l.sub(" o", polytype[1])
            polytype1 = r.sub("o ", polytype1)
            # Split the string of exponents into a list of strings.
            polytype1 = polytype1.split()
            expons = []
            for exp in polytype1:
                if not exp.startswith('o'):
                    # If this substring doesn't represent a large exponent:
                    for i in list(exp):
                        expons.append(int(i))
                else: 
                    # If this substring represents a large exponent:
                    exp = exp.strip('o')
                    expons.append(int(exp))
            
            if polytype[0].upper() == "F":
                for expon in expons:
                    type_objects.append(AtomicPolyType(PolyType.Fermat, 
                                                       [expon]))
                    tot_vars += 1
            elif polytype[0].upper() == "C":
                type_objects.append(AtomicPolyType(PolyType.Chain, expons))
                tot_vars += len(expons)
            elif polytype[0].upper() == "L":
                type_objects.append(AtomicPolyType(PolyType.Loop, expons))
                tot_vars += len(expons)
            elif polytype[0].upper() == "RC":
                type_objects.append(AtomicPolyType(PolyType.RChain, expons))
                tot_vars += len(expons)
            elif polytype[0].upper() == "RL":
                type_objects.append(AtomicPolyType(PolyType.RLoop, expons))
                tot_vars += len(expons)

        
        if not names:
            if tot_vars <= 4:
                names = "xyzw"
            else:
                names = ["X" + str(i + 1) for i in range(tot_vars)]
        
        # Edited July 2012, Scott Mancuso
        # Added the extra parameter var_order so that the order of terms in the
        # polynomial ring could be defined separately from the polynomial
        # itself. This makes it possible to have atomic types that span
        # arbitrary variables in the ring, allowing us to use this method to
        # truly create any invertible singularity in any polynomial ring.
        try:
            if set(names) != set(var_order):
                # Silently ignore var_order if it contradicts names. Is this
                # what we want, or should an exception be raised?
                var_order = names
        except TypeError:
            # var_order wasn't set. Use names instead.
            var_order = names
        R = PolynomialRing(coefficient_ring, tot_vars, 
                           list(var_order)[:tot_vars], order='lex')
        # Convert `names` from strings to variables.
        gens_dict = R.gens_dict()
        var_names = [gens_dict[name] for name in names[:tot_vars]]
        this_singularity = cls.from_types_and_ring(type_objects, R, var_names)
        this_singularity.polystring = polystring
        return this_singularity
        
    @classmethod
    def icreate(cls, polystring, show_parse=True):
        # Representation in the form F3RC412l37...
        atomic_string = "";
        # List of variable names, in order of appearance in atomic_string.
        variable_names = [];
        
        # Pad with addition signs for parsing.
        polystring = "+" + polystring + "+"
        
        import re
        VAR = r"([a-zA-Z]\w*)"  # CAPTURES variable name.
        EXP = r"\^?(\d*)"       # CAPTURES exponent.
        EXP_ONE = r"(?:\^1)?"   # Matches exponent of 1 or no exponent.
        ADD = r"\+"             # Matches addition sign.
        MULT = r"\*"            # Matches multiplication sign.
        
############################################################
#
# FERMAT & CHAIN parsing
#
############################################################
        
        # Will match one monomial.
        search_result = re.search(ADD + VAR + EXP + ADD, polystring)
        if search_result is not None:
            polystring = (polystring[:search_result.start()] + "+" + 
                          polystring[search_result.end():])

        while search_result is not None:
            
            only_one_monomial = True
            
            # Will keep exponents and variables of the chain in reverse order.
            chain_expons_list = []
            chain_vars_list = []
            
            while search_result is not None:
                var_name = search_result.group(1)
                var_exp = (search_result.group(2) if search_result.group(2) != 
                           "" else "1")

                search_result = re.search(ADD + var_name + EXP_ONE + MULT + 
                                          VAR + EXP + ADD, polystring)
                if search_result is None:
                    search_result = re.search(ADD + VAR + EXP + MULT + 
                                              var_name + EXP_ONE + ADD, 
                                              polystring)

                if search_result is not None:
                    polystring = (polystring[:search_result.start()] + "+" + 
                                  polystring[search_result.end():])

                # If there are still more occurances of the variable:
                if re.search(r"\W" + var_name + r"\W", polystring) is not None:
                    raise QSingularityError ("NOT ADMISSIBLE: two many "
                                              "occurances of " + var_name)
                # If it is a Fermat:
                elif search_result is None and only_one_monomial:
                    atomic_string += "F"
                    atomic_string += (var_exp if len(var_exp) == 1 else 
                                      "(" + var_exp + ")")
                    variable_names.append(var_name)
                # It must be a chain:
                else:
                    # If this is the 1st time through:
                    if only_one_monomial:
                        atomic_string += "C"
                    only_one_monomial = False
                    chain_expons_list.append(var_exp if len(var_exp) == 1 else 
                                             "(" + var_exp + ")")
                    chain_vars_list.append(var_name)
            
            while chain_expons_list:
                atomic_string += chain_expons_list.pop()
                variable_names.append(chain_vars_list.pop())
                
            search_result = re.search(ADD + VAR + EXP + ADD, polystring)
            if search_result is not None:
                polystring = (polystring[:search_result.start()] + "+" + 
                              polystring[search_result.end():])
        
############################################################
#
# LOOP parsing
#
############################################################

        # Find the start of the first loop.
        search_result = re.search(ADD + r"\w*" + EXP_ONE + MULT + VAR + EXP + 
                                  ADD, polystring)
        if search_result is None:
            search_result = re.search(ADD + VAR + EXP + MULT + r"\w*" + 
                                      EXP_ONE + ADD, polystring);

        if search_result is not None:
            # Remember start of loop.
            if re.search(ADD + VAR + EXP_ONE + MULT, 
                         search_result.group()) is not None:
                start_var = re.search(ADD + VAR + EXP_ONE + MULT, 
                                      search_result.group()).group(1)
            else:
                start_var = re.search(MULT + VAR + EXP_ONE + ADD, 
                                      search_result.group()).group(1)
            polystring = (polystring[:search_result.start()] + "+" + 
                          polystring[search_result.end():])
        
        while search_result is not None:
            atomic_string += "L"
            loop_expons_list = []
            loop_vars_list = []
            
            while search_result is not None:
                var_name = search_result.group(1)
                var_exp = (search_result.group(2) if search_result.group(2) != 
                           "" else "1")
                
                search_result = re.search(ADD + var_name + EXP_ONE + MULT + 
                                          VAR + EXP + ADD, polystring)
                if search_result is None:
                    search_result = re.search(ADD + VAR + EXP + MULT + 
                                              var_name + EXP_ONE + ADD, 
                                              polystring)

                if search_result is not None:
                    polystring = (polystring[:search_result.start()] + "+" + 
                                  polystring[search_result.end():])

                # If there are still more occurances of the variable.
                if re.search(r"\W" + var_name + r"\W", polystring) is not None:
                    raise QSingularityError ("NOT ADMISSIBLE: two many "
                                              "occurances of " + var_name)
                else:
                    loop_expons_list.append(var_exp if len(var_exp) == 1 else 
                                            "(" + var_exp + ")")
                    loop_vars_list.append(var_name)
            
            if var_name != start_var:
                # If we didn't come back in a loop.
                raise QSingularityError ("NOT ADMISSIBLE: loop failed!" 
                                          + polystring)
            
            while loop_expons_list:
                atomic_string += loop_expons_list.pop()
                variable_names.append(loop_vars_list.pop())
            
            
            # Find the start of the next loop.
            search_result = re.search(ADD + r"\w*" + EXP_ONE + MULT + VAR + 
                                      EXP + ADD, polystring)
            if search_result is None:
                search_result = re.search(ADD + VAR + EXP + MULT + r"\w*" + 
                                          EXP_ONE + ADD, polystring);

            if search_result is not None:
                # Remember start of loop.
                if re.search(ADD + VAR + EXP_ONE + MULT, 
                             search_result.group()) is not None:
                    start_var = re.search(ADD + VAR + EXP_ONE + MULT, 
                                          search_result.group()).group(1)
                else:
                    start_var = re.search(MULT + VAR + EXP_ONE + ADD, 
                                          search_result.group()).group(1)
                polystring = (polystring[:search_result.start()] + "+" + 
                              polystring[search_result.end():])
            
        # If characters other than addition signs left over:
        if re.search(r"[^\+]", polystring) is not None :
            raise QSingularityError ("NOT ADMISSIBLE: " + polystring[1:-1] 
                                      + " left over after parsing")

        if show_parse:
            print(atomic_string)
            # Print variables, removing apostrophes and quotes.
            print(re.sub("['\"]", "", str(variable_names)))
        return (atomic_string, variable_names)   
  
    @lazy_attr
    def matrix(self):
        """
        Returns the appropriate exponent matrix, with the preferred ordering of
        monomials.

        EXAMPLES::

            sage: W = QSingularity.create("RL3456")
            sage: W.matrix
            [3 0 0 1]
            [1 4 0 0]
            [0 1 5 0]
            [0 0 1 6]
            sage: Wt = W.transpose()
            sage: Wt.matrix
            [3 1 0 0]
            [0 4 1 0]
            [0 0 5 1]
            [1 0 0 6]
            sage: Wt.matrix == W.matrix.transpose()
            True

        As we would hope....  Also works with restriction::

            sage: W = QSingularity.create("F4567")
            sage: Wr = W.restrict([1, 3])
            sage: Wr.matrix
            [5 0]
            [0 7]
            
        """
        
        if self.nvariables == 0:
            return matrix([[]])
        def compare_exp(l, m):
            return l.index(max(l)) - m.index(max(m))

        expons = [list(e) for e in self.poly.exponents()]

        expons = [[e[i] for i in [self.poly.parent().gens().index(v) for v in 
                                  self.poly.variables()]] for e in expons]
        expons=sorted(expons,key = lambda x: x.index(max(x))) #cmp=compare_exp)
        return matrix(expons)
    
    def _matrix_(self):
        """Allows use of the built-in Sage function :func:`matrix`."""
        return self.matrix
    
    @lazy_attr
    def dimen(self):
        """ 
        Computes the dimension of each weighted sector of the Milnor Ring by
        computing the Poincare polynomial.
        
        OUTPUT:

        - Returns a dictionary with the weights as keys and corresponding
          dimensions as values
         
        EXAMPLES::
        
            sage: W = QSingularity.create("L47")
            sage: W.dimen
            {0: 1, 2/3: 4, 1/3: 2, 10/9: 2, 1: 2, 8/9: 3, 1/9: 1, 2/9: 2,
                5/9: 3, 4/9: 3, 7/9: 3, 11/9: 1, 4/3: 1}
            
            sage: W = QSingularity.create("L739F2")
            sage: d = W.dimen
            sage: d[7/10]
            14
            
        """
        
        # Theorem used to compute Poincare polynomial:
        # To find the Poincare polynomial p(t) of a quasihomogeneous function
        # with weights (q_1, ..., q_n)
        # p(t) = \prod_{i=1}^{n} (t^{1 - q_i} - 1)\over (t^{q_i} - 1)
        
        # self.q is the lazy attribute that gives the weights of the 
        # singularity.
        weights = self.q
        numvar = len(weights)
        leastcm = 1
        
        # In order to compute the quotient of polynomials, the weights are
        # multiplied by the least common multiple of their denominators in order
        # to turn them into integers.
        for i in range(numvar):
            leastcm = lcm(leastcm, weights[i].denominator())
        
        # Computation of the Poincare polynomial by the above mentioned method.  
        t = var('t')
        R = PolynomialRing(QQ, "t")
        polyf = 1
        polyg = 1
        for i in range(numvar):
            polyf = R(polyf*(t**(leastcm - weights[i]*leastcm) - 1))
        for i in range(numvar):
            polyg = R(polyg*(t**(weights[i]*leastcm) - 1))
        polyh = R(polyf/polyg)
        
        # The integer exponents are changed back into rational exponents by
        # diving by the least common multiple.
        dictd = dict([])
        deg = polyh.degree()
        coeff = polyh.list()
        for i in range(deg + 1):
            if coeff[i] != 0:  # Terms with zero coefficient are ignored.
                dictd[i / leastcm] = coeff[i]
        
        return dictd
        
    def poincare(self):
        """ 
        Computes the Poincare polynomial of this singularity based on the
        coefficients and exponents given in the lazy attribute
        :meth:`~QSingularity.dimen`.
        
            - Prints the Poincare polynomial with ``t`` as a variable
            - Does not return any values
         
        EXAMPLES::
        
            sage: W = QSingularity.create("L47")
            sage: W.poincare()
            The Poincare polynomial for this singularity is
            t^4/3 + t^11/9 + 2*t^10/9 + 2*t + 3*t^8/9 + 3*t^7/9 + 4*t^2/3 +
            3*t^5/9 + 3*t^4/9 + 2*t^1/3 + 2*t^2/9 + t^1/9 + 1
            
            sage: W = QSingularity.create("L739F2")
            sage: W.poincare()
            The Poincare polynomial for this singularity is
            t^2 + 2*t^19/10 + 3*t^9/5 + 5*t^17/10 + 7*t^8/5 + 9*t^3/2 + 12*t^7/5
            + 14*t^13/10 + 16*t^6/5 + 17*t^11/10 + 17*t + 17*t^9/10 + 16*t^4/5 +
            14*t^7/10 + 12*t^3/5 + 9*t^1/2 + 7*t^2/5 + 5*t^3/10 + 3*t^1/5 +
            2*t^1/10 + 1
            
        """
        
        dictd = self.dimen
        listl = sorted(dictd, reverse=True)
        polystr = ""
        for i in range(len(listl) - 1):
            expon = listl[i]
            if dictd[expon] != 0:  # Terms with zero coefficient are ignored.
                if expon == 1:  # The term with an exponent of one.
                    exponent = ""
                else:
                    exponent = "^" + str(expon)
                # If the coefficient is one, the coefficient is ignored.
                if dictd[expon] == 1:
                    polystr = polystr + "t" + exponent + " + "
                else:
                    polystr = (polystr + str(dictd[expon]) + "*t" + exponent + 
                               " + ")
        # Every Poincare polynomial by the above mentioned method will have an
        # ending term of "1".
        polystr = polystr + "1"
        print ("The Poincare polynomial for this singularity is " + "\n" + 
               polystr)
    
    @lazy_attr
    def q(self):
        """
        Returns a tuple of the weights of the variables in this singularity.
        
        EXAMPLES::
        
            sage: W = QSingularity.create("x^2*y+y^3*x")
            L32
            [y, x]
            sage: W.q
            (2/5, 1/5)
            
            sage: W = QSingularity.create("C365L83")
            sage: W.q
            (13/45, 2/15, 1/5, 2/23, 7/23)
        
        """
        
        if self.nvariables == 0:
            return []
        m = self.matrix
        v = vector([1]*m.ncols())
        return tuple(m.solve_right(v))

    @classmethod
    def empty(cls):
        return cls([])

    @lazy_attr
    def expons(self):
        """
        Return a list of the non-1 exponents of this singularity.

        EXAMPLES::
        
            sage: W = QSingularity.create("C334")
            sage: W.expons
            [3, 3, 4]
    
            sage: W = QSingularity.create("RC374L99F6")
            sage: W.expons
            [3, 7, 4, 9, 9, 6]
            
        """
        
        a = []
        for atomic in self.atomics:
            a += atomic.expType.expon
        return a
    
    @lazy_attr
    def vars(self):
        """
        Return a list of the variable names of this singularity.

        EXAMPLES::
        
            sage: W = QSingularity.create("x^2 + y^2 + y*z^3", show_parse=False)
            sage: W.vars
            [x, y, z]
    
            sage: W = QSingularity.create("RC374L99F6")
            sage: W.vars
            [X1, X2, X3, X4, X5, X6]
            
        """
        
        a = []
        for atomic in self.atomics:
            a += atomic.vars
        # Put `a` in the order that the variables would show up in the
        # polynomial ring (largest first).
        a.sort(reverse=True)
        return a
        
    @lazy_attr
    def atomics_str(self):
        """
        Return a list of the atomic polynomials of this singularity.

        EXAMPLES::
        
            sage: W = QSingularity.create("c34")            
            sage: W.atomics_str
            ['C(3, 4)']
            
            sage: W = QSingularity.create("L355C23F8")
            sage: W.atomics_str
            ['L(3, 5, 5)', 'C(2, 3)', 'F(8)']

            sage: W = QSingularity.create("x^5*z+z^7*y+w^8*x+y^9")
            C8579
            [w, x, z, y]
            sage: W.atomics_str
            ['C(8, 5, 7, 9)']
            
            sage: W = QSingularity.create("x^5*z+z^7*w+w^8*x+y^9")
            F9L785
            [y, z, w, x]
            sage: W.atomics_str
            ['F(9)', 'L(7, 8, 5)'] 
                    
        """
        
        a = []
        for atomic in self.atomics:
            a.append(atomic.str)
        return a

    @lazy_attr
    def milnor_ring(self):
        """
        Return a special basis for the Milnor ring, as described in Krawitz,
        due to Kreuzer.
        
        .. TODO:: Add some more examples and check them!!!

        EXAMPLES::

            sage: W = QSingularity.create("RC334")

            sage: W.milnor_ring
            [1, z, z^2, z^3, y, y*z, y*z^2, y^2, y^2*z, y^2*z^2, x, x*z,
                x*z^2, x*z^3, x*y, x*y*z, x*y*z^2, x*y^2, x*y^2*z, x*y^2*z^2,
                x^2, x^2*z, x^2*z^2, x^2*y, x^2*y*z, x^2*y*z^2, x^2*y^2,
                x^2*y^2*z, x^2*y^2*z^2]

        The dimension of the Milnor Ring should be given by
        :meth:`~Singularity.Singularity.mu`::

            sage: len(W.milnor_ring)
            29
            sage: W.mu
            29
            
        """
        debugatomics = self.atomics
        debuglist = [atomic.milnor_ring() for atomic in debugatomics]
        mr = cartesian_product(debuglist)
        mr = [prod(l) for l in mr]

        return mr

    def restrict(self, fixed):
        """
        Return the restriction of this :class:`~QSingularity.QSingularity`.
        
        INPUT:
        
        - ``fixed`` - A set of (0 based) indexes of the variables to keep.
         
        OUTPUT:
        
        - A new :class:`~Qsingularity.QSingularity` object that is the 
          restriction of this one to the indexes specified.
         
        EXAMPLES::
        
            sage: W = QSingularity.create("RC323")
            sage: W
            Singularity defined by polynomial x^3 + x*y^2 + y*z^3.
            
            sage: W.restrict([0, 1])
            Singularity defined by polynomial x^3 + x*y^2.
            
            sage: W.restrict([0])
            Singularity defined by polynomial x^3.
            
            sage: W.restrict([])
            Singularity defined by polynomial 0.
            
            sage: W.restrict([0, 1, 2])
            Singularity defined by polynomial x^3 + x*y^2 + y*z^3.
        
        Notice that you can only restrict to sets of indexes that are the fixed 
        locus of a group element::
        
            sage: W.restrict([2])
            Traceback (most recent call last):
            ...
            QSingularityError: Bad input to restrict in AtomicPoly class for 
            RChain![2]
            
        """
        fixed = list(fixed)
        fixed.sort()
        if fixed == []:
            return self.empty()
        for i in fixed:
            if not (i >= 0 and i < self.nvariables):
                raise QSingularityError( "Bad fixed locus indexes to restrict!")

        ratomics = []
        curIndex = 0
        for a in self.atomics:
            fixeda = []
            for i in fixed:
                var_name = self.vars[i]
                try:
                    index = a.vars.index(var_name)
                except ValueError:
                    # This variable doesn't appear in this atomic.
                    pass
                else:
                    fixeda.append(index)
            ar = a.restrict(fixeda)
            if ar.expType.type != PolyType.Empty:
                ratomics.append(ar)
            curIndex += len(a.expType.expon)
        return QSingularity(ratomics)

    def transpose(self, newvars = []):
        """
        Return the transpose of this polynomial.

        INPUT:
        
        - ``newvars`` -- (optional) A list of new variables for the transpose 
          polynomial.  If none are given, the variables of the original 
          polynomial are used.  You can also pass in a string of one-character 
          variable names.

        OUTPUT:
        
        - A new :class:`~QSingularity.QSingularity` object that represents the 
          B-H transpose of this singularity.

        EXAMPLES::

            sage: Wchain = QSingularity.create("C234"); Wchain
            Singularity defined by polynomial x^2*y + y^3*z + z^4.

            sage: Wchain.transpose()
            Singularity defined by polynomial x^2 + x*y^3 + y*z^4.

        The double transpose takes you back to the original::

            sage: Wchain.transpose().transpose()
            Singularity defined by polynomial x^2*y + y^3*z + z^4.

        You can change variable names when you transpose, if you like::

            sage: Wchain.transpose("XYZ")
            Singularity defined by polynomial X^2 + X*Y^3 + Y*Z^4.

        Some loop examples::

            sage: Wloop = QSingularity.create("L8888"); Wloop
            Singularity defined by polynomial x^8*y + x*w^8 + y^8*z + z^8*w.

            sage: Wloop.transpose()
            Singularity defined by polynomial x^8*w + x*y^8 + y*z^8 + z*w^8.

            sage: Wloop.transpose(["xbar", "ybar", "zbar", "wbar"])
            Singularity defined by polynomial xbar^8*wbar + xbar*ybar^8 +
            ybar*zbar^8 + zbar*wbar^8.

        Fermat types are self-dual::

            sage: Wfer = QSingularity.create("F7", "X"); Wfer
            Singularity defined by polynomial X^7.

            sage: Wfer.transpose()
            Singularity defined by polynomial X^7.

        A complicated example::

            sage: W = QSingularity.create("RC996L456F98"); W
            Singularity defined by polynomial X1^9 + X1*X2^9 + X2*X3^6 + X4^4*X5
            + X4*X6^6 + X5^5*X6 + X7^9 + X8^8.

            sage: W.transpose()
            Singularity defined by polynomial X1^9*X2 + X2^9*X3 + X3^6 + X4^4*X6
            + X4*X5^5 + X5*X6^6 + X7^9 + X8^8.
            
        """
        
        # Find the coefficient ring for this QSingularity.
        coefficient_ring = self.ring.base_ring()
        if newvars != []:
            if len(newvars) != self.nvariables:
                raise QSingularityError ("Wrong number of new variables")
            R = PolynomialRing(coefficient_ring, list(newvars))
            newvars = R.gens()
        else:
            newvars = self.poly.variables()
        
        # Replace each atomic type with its transpose.
        new_polystring = self.polystring.replace("L", "RL").replace("C", "RC")
        # Replace double reverses.
        new_polystring = new_polystring.replace("RR", "")
        return self.create(new_polystring, [str(newvar) for newvar in newvars], coefficient_ring)
#         curIndex = 0
#         newatomics = []
#         for a in self.atomics:
#             newatomics.append(a.transpose(newvars[curIndex:(curIndex + 
#                               len(a.expType.expon))]))
#             curIndex += len(a.expType.expon)
#         return QSingularity(newatomics)


class QSingularityError(SingularityError):
    """
    This exception is raised when the user attempts to create an inadmissible
    :class:`~QSingularity.QSingularity`.
    
    """
    pass


def flatten(l):
    """
    A utility function required to compute the tensor product of Milnor Rings.  
    Copied off the internet.
    
    """
    
    out = []
    for item in l:
        if isinstance(item, (list, tuple)):
            out.extend(flatten(item))
        else:
            out.append(item)
    return out
