"""
This module contains:

    Singularity
        Methods:
            create
            get_weighted_degree
            hessian_det
            hessian
            restrict
            is_zero
            get_ring
        Attributes:
            milnor_ring
            modality
            QHDim
            milnor_ring_ring
            ngens
            nvariables
            vars
            monomials
            q
            matrix
            mu
            central_charge

AUTHORS:

    - Drew Johnson (2010-2011) Initial design and implementation
    - Julian Tay (Aug 2012) Documentation

"""
# if not __name__ == '__main__':  # i.e. if this is being imported rather than 
                                # read as a load or attach.
try:
    from sage.all import *
except ImportError:
    print("Didn't import Sage!!!")

import sys
import itertools as it
if "." not in sys.path: sys.path.insert(0,".")

from LazyAttr import lazy_attr

# For debugging purposes only.
def get_ring(polynomial):
    tot_vars = len(polynomial.variables())
    names = ""              
        
    for var in polynomial.variables():
        names += str(var)
    
    import sage.rings.polynomial.multi_polynomial_libsingular as mpl
    ring = mpl.MPolynomialRing_libsingular(QQ, tot_vars, list(names)[:tot_vars],
                                           order='lex')
    return ring


class Singularity(SageObject):
    """
    Represents a quasihomogeneous polynomial, and a Sage ring that it lives in.
    
    CONSTRUCTOR:

    - ``polynomial`` -- A Sage polynomial.
    - ``term_order`` -- Specify the term order for this :class:`Singularity`
      (will affect the appearance of the milnor ring basis).
    
    .. NOTE::
    
        The user should not use the constructor to create instances of the
        :class:`Singularity` class; the :meth:`create` method should be used
        instead.
        If the constructor is used, many of the object's methods will not work.
        This is because the constructor does not check for non-degeneracy, nor
        does it alter the parent ring of the polynomial. For example, the 
        singularity :math:`W = x + y` is not non-degenerate::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity(x + y)
            sage: W.ring
            Multivariate Polynomial Ring in x, y, z over Rational Field
            sage: W._is_nondegenerate()
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
            
            sage: R.<x,y>=QQ[]
            sage: W=Singularity(x^3*y + (-3/(4^(1/3)))*x^2*y^3 + y^7)
            sage: W._is_nondegenerate()
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
        
        See the :func:`Singularity.create` method for more examples.
    
    """
    def __init__(self, polynomial, term_order='lex'):
        
        self.poly = polynomial    
        self.ring = self.poly.parent()
        self.term_order = term_order
    
    @classmethod
    def create(cls, polynomial, term_order='lex', check_nondegenerate=True, 
               prove_nondegenerate=True):
        """
        Use this to make a quasihomogeneous non-degenerate singularity that will
        be compatible with the FJRW ring constructing methods.
        
        INPUT:
        
        - ``polynomial`` -- A Sage polynomial that describes this
          :class:`Singularity`.
        - ``term_order`` -- Specify the term order for this :class:`Singularity`
          (will affect the appearance of the milnor ring basis). Defaults to 
          'lex'.
        - ``check_nondegenerate`` -- Defaults to ``True``. If set to ``True``,
          this method will check that the polynomial is non-degenerate.
        - ``prove_nondegenerate`` -- Defaults to ``True``. If set to ``True``,
          this method will use the :meth:`_is_nondegenerate` method to solve the
          necessary system of equations and guarantee that this polynomial is
          non-degenerate. If set to ``False``, it will use the
          :meth:`_is_likely_nondegenerate` method to determine if a generic
          polynomial of this form is non-degenerate (i.e. not taking the
          coefficients into account).
        
        OUTPUT:
        
        - A :class:`Singularity` object.
        
        EXAMPLES:
    
        To create a quasihomogeneous non-degenerate Singularity, use the
        :func:`create` method::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z); W
            Singularity defined by polynomial x^3 + x*y*z + y^3 + z^3.
        
            sage: W = Singularity.create(x^2*z + y^4*z + z^3 + x^2*y^2); W
            Singularity defined by polynomial x^2*y^2 + x^2*z + y^4*z + z^3.
        
        The :func:`create` method trims the parent ring down to the size of the
        singularity:: 

            sage: W = Singularity.create(x^29); W
            Singularity defined by polynomial x^29.
            sage: W.ring
            Multivariate Polynomial Ring in x over Rational Field

        This method automatically checks that the polynomial contains no
        :math:`x_ix_j` term::    
            
            sage: W = Singularity.create(x^3 + y^4 + z^2 + 5*z*y)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial contains x_i * x_j term
            
        We can specify the term_order for the underlying polynomial ring of this
        :class:`Singularity`, which will affect the appearance of the basis for
        the Milnor ring::
        
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z,
            ...   term_order='degrevlex')
            sage: W.milnor_ring
            [1, z, y, x, z^2, y*z, x*z, z^3]
            
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z, 
            ...   term_order='invlex')
            sage: W.milnor_ring
            [1, x, y, z, x^2, x*y, y^2, x^3]
            
        The :meth:`create` method checks that the input is non-degenerate,
        unless requested not to::
        
            sage: W = Singularity.create(x^4 + x^2*y^4 + x^3*y^2)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
            
            sage: W = Singularity.create(x + y)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
        
        A faster algorithm is available for checking non-degeneracy via the
        method :meth:`Singularity._is_likely_nondegenerate`. This method can be
        used by setting ``prove_nondegenerate=False`` ::
        
            sage: W = Singularity.create(x^4 + x^2*y^4 + x^3*y^2, 
            ...   prove_nondegenerate=False)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
        
        However, be aware that if the wrong coefficients are chosen, the wrong
        result may be returned::
        
            sage: W = Singularity.create(x^3*y + (-3/(4^(1/3)))*x^2*y^3 + y^7, 
            ...   prove_nondegenerate=False)
            sage: W = Singularity.create(x^3*y + (-3/(4^(1/3)))*x^2*y^3 + y^7)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
            sage: W = Singularity.create(x^3*y + x^2*y^3 + y^7, 
            ...   prove_nondegenerate=True)

            sage: R.<x, y, z, w> = QQ[]
            sage: W = Singularity.create(x^6*z + x*y^5 + y*w^2 + z^3*x + x*y*z*w
            ...   + x^4*y^3 + x^5*w + x^2*y*z^2 + x^7*y + x^2*y^2*w + x^3*y^2*z 
            ...   + y^4*z + z^2*w, prove_nondegenerate=False)
            sage: W._is_nondegenerate()
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate            
        
        But we may request that the :meth:`create` method not check for
        non-degeneracy::
        
            sage: W = Singularity.create(x + y, check_nondegenerate=False); W
            Singularity defined by polynomial x + y.
            
        The :meth:`create` method checks that the input is quasihomogeneous::
        
            sage: W = Singularity.create(x^3*y + y^2*x + x^2*y^4)
            Traceback (most recent call last):
            ...
            SingularityError: Singularity is not quasi-homogeneous
    
        :class:`Singularity` objects are also callable::
        
            sage: W(4, 5)
            9   
        
        
        .. NOTE::
        
            To create a :class:`Singularity` object with complex (or variable) 
            coefficients, create a ring over QQbar (or over QQ[c0, c2], etc.) of
            the precise size needed and use the constructor for this class, not
            the :func:`create` method (check by hand that your polynomial 
            satisfies all necessary hypotheses). Use `sqrt(QQbar(-1))` for I.
        
        See [FJRW]_.
        
        """
        tot_vars = len(polynomial.variables())
        names = [str(var) for var in polynomial.variables()]
        
        # Create a new polynomial ring over the same base as the original but 
        # with the correct number of variables.
        R = PolynomialRing(polynomial.parent().base(), tot_vars, 
                           list(names)[:tot_vars], order=term_order) 
                           
        # polynomial is passed into the new polynomial ring R as a string so as
        # to prevent variables from being lost due to coersion between rings.
        # (Julian Tay, Aug 2012; checked by Scott Mancuso)
        new_poly = Singularity(R(str(polynomial)), term_order)
        
        # Check that the polynomial satisfies all of the hypotheses.
        new_poly._has_no_xy_term()
        
        # This will also check for quasi-homogeneousness.
        new_poly.q
        
        # If requested by user, check that the polynomial is non-degenerate.
        if check_nondegenerate:
            if prove_nondegenerate:
                new_poly._is_nondegenerate()
            else:
                new_poly._is_likely_nondegenerate()
        
        return new_poly
    
    @classmethod
    def make_rational_weights(cls, *weights):
        """
        Convert an integer weight system to a rational weight system.
        
        INPUT:
        
        - ``weights`` -- A weights system, passed in one at a time as integer
          values. The last value should be the weighted degree.
        
        OUTPUT:
        
        - A tuple with the same weight system, scaled so the weighted degree is 
          one.
        
        """
        return tuple(q/weights[-1] for q in weights[:-1])
    
    @classmethod
    def from_weights(cls, *weights, **keyword_args):
        """
        Factory method. Get a :class:`~Singularity` by passing in the weights
        of the polynomial.
        
        Keyword arguments are as with :meth:`~Singularity.create`, plus a few
        others for explicitly controlling the polynomial ring being created (a
        la :meth:`~QSingularity.create`).
        
        INPUT:
        
        - ``weights`` -- The weights of the desired polynomial, passed
          in one at a time as rational values.
        - ``names`` -- (optional) The names of the variables, given as a list
          of strings.  You can also pass in a string of one character
          variable names.  If you don't specify them, the method will
          choose ``x``, ``y``, ``z``, and ``w`` for less that four
          variables, and ``X1, ... , XN`` for N > 4 variables.
        - ``coefficient_ring`` -- (optional) The coefficient ring of the
          polynomial. Should be a field. Defaults to the rationals.
        - ``term_order`` -- Specify the term order for this :class:`Singularity`
          (will affect the appearance of the milnor ring basis). Defaults to 
          'lex'.
        - ``check_nondegenerate`` -- Defaults to ``True``. If set to ``True``,
          this method will check that the polynomial is non-degenerate.
        - ``prove_nondegenerate`` -- Defaults to ``False``. If set to ``True``,
          this method will use the :meth:`_is_nondegenerate` method to solve the
          necessary system of equations and guarantee that this polynomial is
          non-degenerate. If set to ``False``, it will use the
          :meth:`_is_likely_nondegenerate` method to determine if a generic
          polynomial of this form is non-degenerate (i.e. not taking the
          coefficients into account).
        - ``invertible`` -- If ``True``, only return invertible polynomials.
          Defaults to ``False``.
        - ``poly_list`` -- If given, this should be a list where all of the
          possible polynomials can be stored, or anything besides ``None``. In
          either case the list is also returned. Otherwise the user is asked
          which polynomial they want.
        - ``n_monoms`` -- (optional) The number of monomials the polynomial
          should contain. If not specified, all possible polynomials are found.
        - ``test_mode`` -- (optional) Defaults to ``False``. If set to ``True``,
          the method will be run in test mode, meaning that just the first
          ``Singularity`` found will be returned.
        
        OUTPUT:
        
        - A :class:`~Singularity` with the given weights, or a list of possible
          singularities.
        
        EXAMPLES::
        
        ***Lookup WeightedIntegerVectors class***
        
        """
        # Remove extra keywords so they aren't passed to other methods.
        invertible = keyword_args.pop("invertible", False)
        poly_list = keyword_args.pop("poly_list", None)
        n_monoms = keyword_args.pop("n_monoms", 0)
        test_mode = keyword_args.pop("test_mode", False)
        # If the weights are passed in as integers, convert them to rationals.
        if weights[0] in ZZ:
            weights = cls.make_rational_weights(*weights)
        n_vars = len(weights)
        # `suppress` is only used if the user gets a certain exception they need
        # to suppress.
        suppress = keyword_args.pop("suppress", False)
        
        # Get a list of the maximum power possible for each variable.
        max_powers = [floor(~qx) for qx in weights]  # ~ inverts things.
        all_powers_iter = it.product(*[range(mp + 1) for mp in max_powers])
        
        # Get the integer form of the weights.
        common_denom = lcm([q.denominator() for q in weights])
        integer_weights = [q*common_denom for q in weights]
        weighted_vectors = WeightedIntegerVectors(common_denom, integer_weights).map(tuple)
        QHDim = weighted_vectors.cardinality()
        
        n_possibilities = sum((binomial(QHDim, n) 
                               for n in range(n_vars, QHDim+1)))
        
#         # Make a list of tuples where each tuple gives the powers of the
#         # variables in a monomial of total degree one.
#         deg_one_powers = []
#         for power_list in all_powers_iter:
#             # Zip weights and powers.
#             td = sum([prod(wd) for wd in it.izip(power_list, weights)]) 
#             if td == 1:
#                 deg_one_powers.append(power_list)
#         
#         QHDim = len(deg_one_powers)
#         n_possibilities = sum([binomial(QHDim, n) 
#                                for n in range(n_vars, QHDim+1)])
        
        # If deg_one_powers is at all long, it will take an impossibly long time
        # to run through all possible combinations. We will instead ask the user
        # to specify the number of monomials they want in the polynomial.
        if n_possibilities > 100 and not (n_monoms or invertible or test_mode):
            n_monoms = raw_input("There are %d possible NDQH "
                    "polynomials with weight system %s. In order to keep "
                    "computations reasonable, please enter the number of "
                    "monomials you would like in your polynomial (%d-%d): " 
                    % (n_possibilities, weights, n_vars, QHDim))
            while True:
                if n_monoms == "all":
                    # If they insist on computing all of them, let them.
                    n_monoms = 0
                    break
                try:
                    n_monoms = int(n_monoms)
                    if not n_vars <= n_monoms <= QHDim:
                        raise ValueError
                except ValueError:
                    n_monoms = raw_input("Invalid entry. Please try again: ")
                else:
                    break
        
        if n_monoms:
            monom_combos = Subsets(weighted_vectors, n_monoms)
        elif invertible:
            monom_combos = Subsets(weighted_vectors, n_vars)
        else:
            monom_combos = Subsets(weighted_vectors)
        # Only include those combos with enough monomials.
        monom_combos = monom_combos.filter(lambda x: len(x) >= n_vars)
        
        # We use some known facts about NDQH singularities to filter our
        # selection.
        # Check that no variable appears in every monomial (proved by Scott
        # Mancuso).
        if n_vars > 2:
            monom_combos = monom_combos.filter(lambda x: 
                                               not any(all(y) for y in zip(*x)))
        # Check that every variable appears at least once.
        monom_combos = monom_combos.filter(lambda x: 
                                           all(any(y) for y in zip(*x)))
        
        all_sings = []
        try:
            for monom_combo in monom_combos:
                if len(monom_combo) < n_vars:
                    # The polynomial must have at least as many monomials as it
                    # does variables.
                    # This should have been taken care of above.
                    raise AssertionError
                    continue
                # No variable can appear in every monomial if we have more than
                # two variables, so throw these out.
                if n_vars > 2:
                    # Organize exponents by variable instead of monomial.
                    expons_by_var = zip(*monom_combo)
                    if any(all(a) for a in expons_by_var):
                        # This should have been taken card of above.
                        raise AssertionError
                        continue
            
                try:
                    sing = Singularity.from_expons(*monom_combo, **keyword_args)
                except SingularityError:
                    # This poly is not NDQH.
                    continue
                else:
                    if sing.nvariables != n_vars:
                        continue
                all_sings.append(sing)
                if test_mode:
                    break
        except KeyboardInterrupt:
            # Allow the user to interrupt the process and return whatever we've
            # found so far.
            print("*"*80)
            print("Computation interrupted! Not all polynomials were found.")
            print("*"*80)
        
        if not all_sings:
            suffix = " and %d monomials" % n_monoms if n_monoms else ""
            raise SingularityError ("No NDQH polynomial exists with this "
                                     "weight system%s." % suffix)
        # Check which ones are invertible.
        all_invertibles = [W for W in all_sings if W.is_invertible]
        
        # If something happens which we aren't sure is possible, we want to know
        # about it. However, we also want to allow the user to continue working
        # as normal, so we'll give them the option of passing a "secret" keyword
        # arg.
        if not all_invertibles and all_sings and (not n_monoms or 
                                                  n_monoms == n_vars):
            try:
                raise SingularityError (
                        "The weight system %(weights)s corresponds to the "
                        "noninvertible polynomial(s) %(all_sings)s but not to "
                        "any invertible polynomials. This is interesting and "
                        "should be reported to Dr. Jarvis or Scott Mancuso "
                        "immediately.\n\nTo suppress this error message, set "
                        "the keyword argument `suppress` to `True`." % locals())
            except SingularityError:
                if not suppress:
                    raise
        
        if invertible:
            all_sings = all_invertibles
        
        # We compare to `None` because an empty list is a perfectly acceptable
        # entry.
        if poly_list is not None:
            try:
                poly_list[:] = all_sings
            except TypeError:
                pass
            finally:
                return all_sings
        
        if len(all_sings) == 1:
            return all_sings[0]
        else:
            all_sings.sort()
        
        suffix = " and %d monomials" % n_monoms if n_monoms else ""
        print ("There are %d%s NDQH polynomials with weight system %s%s. "
               "They are: " % (len(all_sings), 
                               " invertible" if invertible else "", weights, 
                               suffix))
        for i in range(len(all_sings)):
            print("%d:  %s" %(i, all_sings[i]))
        # Let the user pick which one they want.
        selected = raw_input("Which one would you like? \nYou can also type 'all' or a space-separated list of the numbers you want in order to get a list back.\n")
        while True:
            if selected == "all":
                return all_sings
            try:
                if not selected:
                    raise IndexError
                selected = int(selected)
                selected = all_sings[selected]
            except ValueError:
                try:
                    selected = [int(sel) for sel in selected.split()]
                    selected = [all_sings[sel] for sel in selected]
                except (ValueError, IndexError):
                    selected = raw_input("Invalid entry. Please select again: ")
                else:
                    return selected
            except IndexError:
                selected = raw_input("Invalid entry. Please select again: ")
            else:
                return selected
    
    @classmethod
    def from_expons(cls, *expons, **keyword_args):
        """
        Factory method. Create a :class:`~Singularity` by passing in the
        exponents of the polynomial. 
        
        Keyword arguments are as with :meth:`~Singularity.create`, plus a few
        others for explicitly controlling the polynomial ring being created (a
        la :meth:`~QSingularity.create`).
        
        INPUT:
        
        - ``expons`` -- The exponents of the desired polynomial, passed in as a
          single list of integers for each monomial in the polynomial.
        - ``names`` -- (optional) The names of the variables, given as a list
          of strings.  You can also pass in a string of one character
          variable names.  If you don't specify them, the method will
          choose ``x``, ``y``, ``z``, and ``w`` for less that four
          variables, and ``X1, ... , XN`` for N > 4 variables.
        - ``coefficient_ring`` -- (optional) The coefficient ring of the
          polynomial. Should be a field. Defaults to the rationals.
        - ``term_order`` -- Specify the term order for this :class:`Singularity`
          (will affect the appearance of the milnor ring basis). Defaults to 
          'lex'.
        - ``check_nondegenerate`` -- Defaults to ``True``. If set to ``True``,
          this method will check that the polynomial is non-degenerate.
        - ``prove_nondegenerate`` -- Defaults to ``False``. If set to ``True``,
          this method will use the :meth:`_is_nondegenerate` method to solve the
          necessary system of equations and guarantee that this polynomial is
          non-degenerate. If set to ``False``, it will use the
          :meth:`_is_likely_nondegenerate` method to determine if a generic
          polynomial of this form is non-degenerate (i.e. not taking the
          coefficients into account).
        
        OUTPUT:
        
        - A :class:`~Singularity` with the given exponents.
        
        """
        try:
            tot_vars = len(expons[0])
        except TypeError:
            raise SingularityError ("You must pass in a list of exponents for "
                                     "each monomial.")
        if not all([len(x) == tot_vars for x in expons]):
            raise SingularityError ("Each monomial must have the same number "
                                     "of exponents defined.")
        try:
            names = keyword_args.pop("names")
        except KeyError:
            if tot_vars <= 4:
                names = list("xyzw"[:tot_vars])
            else:
                names = ["X%d" % d for d in range(1, tot_vars+1)]

        try:
            coefficient_ring = keyword_args.pop("coefficient_ring")
        except KeyError:
            coefficient_ring = QQ
        
        R = PolynomialRing(coefficient_ring, names, order="lex")
        
        gens_dict = R.gens_dict()
        monoms = []
        for expon in expons:
            # Put each variable in a 2-tuple with its exponent.
            azip = zip(gens_dict, expon)
            monoms.append(mul([gens_dict[g[0]]**g[1] for g in azip]))
        poly = sum(monoms)
        return cls.create(poly, **keyword_args)
    
    def __str__(self):
        return str(self.poly)
    
    def _repr_(self):
        return "Singularity defined by polynomial " + str(self.poly) + "."
    
    def __eq__(self, other):
        if type(self) == type(other):
            return self.poly == other.poly
        return False
    
    def __lt__(self, other):
        if isinstance(other, type(self)):
            return self.poly < other.poly 
        raise TypeError
        
    def _latex_(self):
        """
        Get a LaTeX-friendly version of this singularity.
        
        OUTPUT:
        
        - A string ready to be input to a LaTeX math environment.
        
        EXAMPLES::
            
            sage: from LGModels import *
            
            sage: W = Qs("f34l56")
            sage: latex(W)
            x^{3} + y^{4} + z^{5} w + z w^{6}
                        
            sage: W = Qs("l4565(12)c(10)6839")
            sage: latex(W)
            X_{1}^{4} X_{2} + X_{1} X_{5}^{12} + X_{2}^{5} X_{3} + X_{3}^{6} 
            X_{4} + X_{4}^{5} X_{5} + X_{6}^{10} X_{7} + X_{7}^{6} X_{8} + 
            X_{8}^{8} X_{9} + X_{9}^{3} X_{10} + X_{10}^{9}
        
        """
        return latex(self.poly)
        
    def _has_no_xy_term(self):
        """
        Check that the polynomial has no `x_i x_j` term. For example, `W = xy`
        would fail this test, as would `W = x^2 + y + xz`.
        
            See the :func:`Singularity.create` method for more examples.
        
        """
        for m in self.monomials:
            if ((len(m.variables()) == 2) and (m.degree() == 2 )):
                raise SingularityError ("Polynomial contains x_i * x_j term")
        return True
        
    @lazy_attr
    def milnor_ring(self):
        """
        OUTPUT:
        
        - A set containing a basis for the Milnor ring of this polynomial.
        
        EXAMPLES::
        
            sage: R.<x, y, z, w, s, t> = QQ[]
            sage: W = Singularity.create(x^2*y + y^2*z + z^2*x)
            sage: W.milnor_ring
            [1, z, y, x, z^2, y*z, y^2, z^3]
            
            sage: W = Singularity.create(x^2*y + y^2*z + z^3)
            sage: W.milnor_ring
            [1, z, y, x, z^2, y*z, x*z, y*z^2]
            
            sage: W = Singularity.create(x^4 + y^3 + z^2)
            sage: W.milnor_ring
            [1, y, x, x*y, x^2, x^2*y]
            
            sage: W = Singularity.create(z^(12))
            sage: W.milnor_ring
            [1, z, z^2, z^3, z^4, z^5, z^6, z^7, z^8, z^9, z^10]
            
            sage: W = Singularity.create(z^3*t + t^4)
            sage: W.milnor_ring
            [1, t, z, t^2, z*t, z^2, t^3, z*t^2, z*t^3]
            
            sage: W = Singularity.create(x^2)
            sage: W.milnor_ring
            [1]
        
        """
        groebner_basis = self.poly.jacobian_ideal().groebner_basis()
        degree = 1
        # This is a 1 that is an element of a multivariable polynomial ring.
        basis = [self.poly.variable(0)**0]
        if len(basis) >= self.mu:
            # Return basis when we have gathered enough independent things.
            return basis
        
        while True:
            # Get all possible monomials of degree 'degree' in the ring
            # containing this singularity.
            monomials = self._possible_monomials(degree)
            for monom in monomials:
                # Reduce monomial mod the groebner basis and get rid of any
                # constant.
                monom = monom.reduce(groebner_basis)
                if monom != 0:
                    monom = monom.monomials()[0]
                    if not (monom in basis):
                        basis.append(monom)
                        if len(basis) >= self.mu:
                            # Return basis when we have gathered enough independent
                            # things.
                            return basis
            degree += 1
    
    # I don't get why we need this - right now it is not used.
    def in_basis(self, poly, basis):
        raise Exception ( "Let's depreciate this method!")
        
        if poly in CC:
            return True
        monoms = poly.monomials()
        all_good = True
        for monom in monoms:
            good = False
            for be in basis:
                if monom == be:
                    good = True
                    break
            if not good:
                all_good = False
                break
        return all_good 
    
    # Returns possible monomials of degree 'degree' in polynomial ring in which
    # the singularity lives.
    def _possible_monomials(self, degree):
        expons_list = [[]]
        
        # Loop all x_i except the last; there will be 'nvariables' - 1 of them.
        for x_i in range(0, self.nvariables - 1):
            new_expons_list = []
            for monomial_expons in expons_list:
                # Possible values for the next x_i's expon. Will be 0 through
                # 'degree' - sum of expons already assigned.
                for j in range(0, degree - sum(monomial_expons) + 1):
                    new_expons_list.append(monomial_expons + [j])
            expons_list = new_expons_list
        
        new_expons_list = []
        
        # The exponent of x_n (last variable) must be whatever is left to make
        # the total degree correct.
        for monomial_expons in expons_list:
            new_expons_list.append(monomial_expons 
                                   + [degree - sum(monomial_expons)])
    
        expons_list = new_expons_list
        
        # Turn the list of possible exponents into monomials.
        monomial_list = []
    
        for monomial_expons in expons_list:
                monom = 1
                for i in range(0, self.nvariables):
                    monom *= self.poly.variable(i)**monomial_expons[i]
                monomial_list.append(monom)
    
        return monomial_list
    
    # Returns possible monomials of degree 'degree' in polynomial ring in which
    # the singularity lives.
    def _possible_monomials_alternate(self, degree):
        # I found two built-in Sage methods that do a lot of what the original
        # method did, but they aren't necessarily faster. For computing the
        # milnor ring of X1^3*X2 + X2^2*X3 + X3^3 + X4^4 + X5^5 + X6^4*X7 +
        # X6*X7^4, these were their times, crudely measured:
        # drew's method: 41 seconds
        # IntegerVectors(degree, self.nvariables ): 45 seconds
        # IntegerListsLex(degree, length = self.nvariables): 1 minute 25 seconds
        
        expons_list = list( IntegerVectors(degree, self.nvariables) )
        # Turn the list of possible exponents into monomials.
        monomial_list = []
    
        for monomial_expons in expons_list:
                monom = 1
                for i in range(0, self.nvariables):
                    monom *= self.poly.variable(i)**monomial_expons[i]
                monomial_list.append(monom)
    
        return monomial_list
    
    def get_weighted_degree(self, monomial):
        """
        Return the weighted degree of ``monomial`` with respect to the weights
        of ``self``.
        
        INPUT:
        
        - ``monomial`` -- A monomial with variables taken from the polynomial
          ring containing ``self``.
        
        OUTPUT:
        
        - A rational number giving the weighted degree of ``monomial`` based on
          the weights of ``self``.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^4*y + y^3*x)
            sage: W.q
            (2/11, 3/11)
            sage: W.get_weighted_degree(3*x^3*y^3)
            15/11
            sage: sorted([W.get_weighted_degree(w) for w in W.milnor_ring], 
            ...   reverse=True)
            [12/11, 10/11, 9/11, 8/11, 7/11, 6/11, 6/11, 5/11, 4/11, 3/11, 2/11,
            0]
        
        AUTHOR:
        
        - Scott Mancuso (July 2012)
        
        """
        if monomial not in self.ring:
            raise ValueError ("monomial must only have variables that are in "
                               "this Singularity. Received %s." % monomial)
        
        # Coerce `monomial` into the parent ring of `self`.
        monomial = self.ring(monomial)
        degrees = monomial.degrees()
        weighted_degree = sum([prod(wd) for wd in it.izip(degrees, self.q)])
        return weighted_degree
    
    @lazy_attr
    def modality(self):
        """
        Return the modality of ``self``, i.e.\ the number of elements of the
        Milnor ring basis with weighted degree at least one.
        
        OUTPUT:
        
        - An integer giving the modality of this
          :class:`~Singularity.Singularity`.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^5*y + y^3*x)
            sage: W.q
            (1/7, 2/7)
            sage: W.modality
            2
        
        AUTHOR:
        
        - Scott Mancuso (July 2012)
        
        """
        return len([monom for monom in self.milnor_ring if
                    self.get_weighted_degree(monom) >= 1])
    
    @lazy_attr
    def QHDim(self):
        """
        Return the QHDim of ``self``, i.e.\ the number of monomials in `\mathbb
        C [x_1, \dots, x_n]` of weight `1` with respect to the weight system of
        ``self``.
        
        OUTPUT:
        
        - An integer giving the QHDim of this :class:`~Singularity.Singularity`.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^4*y + y^3*x)
            sage: W.QHDim
            2
            sage: W = Singularity.create(x^5)
            sage: W.QHDim
            1
            sage: W = Singularity.create(x^3*y + y^3*z + z^4)
            sage: W.QHDim
            15
        
        AUTHOR:
        
        - Scott Mancuso (July 2012)
        
        """
        # Get a list of the maximum power possible for each variable in `self`.
        max_powers = [floor(~qx) for qx in self.q]  # ~ inverts things.
        all_powers_iter = it.product(*[range(mp + 1) for mp in max_powers])
        qh_dim = 0
        self.deg_one_powers = []
        for power_list in all_powers_iter:
            # Zip weights and powers.
            td = sum([prod(wd) for wd in it.izip(power_list, self.q)]) 
            if td == 1:
                qh_dim += 1
                self.deg_one_powers.append(power_list)
        return qh_dim
    
    @lazy_attr
    def milnor_ring_ring(self):
        """
        OUTPUT:
        
        - A quotient ring representing the Milnor ring of this polynomial.
        
        """
        
        if self.nvariables == 0:
            return QQ
        return self.poly.parent().quo(self.poly.jacobian_ideal())

    @lazy_attr
    def is_invertible(self):
        """
        Return ``True`` if ``self`` is invertible, ``False`` otherwise.
        
        """
        return self.poly.nvariables() == len(self.poly.monomials())
    
    def hessian_det(self):
        return det(self.hessian())

    def hessian(self):
        if self.nvariables == 0:
            return matrix([[1]])
        return matrix([[self.poly.derivative(X, Y) 
                        for X in self.poly.variables()] 
                        for Y in self.poly.variables()])

    def restrict(self, fixed):
        """
        INPUT:
        
        - ``fixed`` -- a set of integers corresponding to the variables of the
          parent ring to be fixed. The variable indexes are zero-based.
        
        OUTPUT:
        
        - A :class:`Singularity` object that has been restricted to the given
          variables.
        
        EXAMPLES:
        
        First create a singularity W = x^3*y + y^3*z + z^3 + w^4::
        
            sage: R.<x, y, z, w> = QQ[]
            sage: W = Singularity.create(x^3*y + y^3*z + z^3 + w^4); W
            Singularity defined by polynomial x^3*y + y^3*z + z^3 + w^4.
            
        Now restrict to the variables x, y, and w::
        
            sage: Wr = W.restrict([0, 1, 3]); Wr
            Singularity defined by polynomial x^3*y + w^4.
            
        Note that the variables are indexed in the parent ring of the original
        singularity::
        
            sage: Wr.restrict([3])
            Singularity defined by polynomial w^4.
            
        Also, restricting to an empty list (no variables) returns the 0
        Singularity::
        
            sage: W.restrict([])
            Singularity defined by polynomial 0.
        """
        fixed = list(fixed)
        fixed.sort()
        fixed_args = list(self.ring.gens())
        for i in range(0, self.ring.ngens()):
            if i not in fixed:
                fixed_args[i] = 0
        return Singularity(self.poly(fixed_args), term_order=self.term_order)
        

    def is_zero(self):
        """
        OUTPUT: 
        
        - ``True`` if the Singularity is 0; ``False`` otherwise.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^3 + y^3 + z^3)
            sage: W.is_zero()
            False
            
        Now restrict W to be the 0 polynomial::
        
            sage: W_restricted = W.restrict([])
            sage: W_restricted.is_zero()
            True
        """
        
        return self.poly == 0
        
    def __call__(self, *input):
        """
        Evaluates the polynomial at the specified input.
        
        OUTPUT:
        
        - A Sage polynomial that lives in the parent ring of the singularity
          called.
        
        .. TODO::
        
            Is this an appropriate way to handle calls to constant polynomials?
        
        """
        if self.nvariables == 0: 
            return self.poly
        
        try:        
            S = self.get_ring(self.poly)
            # Convert to small ring to call poly, then back to original ring so
            # nothing is changed.
            return self.ring(S(self.poly)(*input))
        except TypeError:
            raise ValueError ("The number of arguments does not match the "
                               "number of variables in the Singularity")
    
    @lazy_attr
    def ngens(self):
        """
        OUTPUT:
        
        - An integer that is the number of generators of the ring that this
          polynomial lives in. This should be useful, for example, when one
          is examining the exponents of this polynomial.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
            sage: W.ngens
            3
            
            sage: W = Singularity.create(x^3*y + y^3)
            sage: W.ngens
            2
            
        """

        return self.poly.parent().ngens()

    @lazy_attr
    def nvariables(self):
        """
        OUTPUT:
        
        - An integer that is the number of variables that are actually in this 
          polynomial.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
            sage: W.nvariables
            3
            
            sage: W = Singularity.create(x^3*y + y^3)
            sage: W.nvariables
            2

        """
        if self.poly == 0:
            return 0
        try:
            return self.poly.nvariables()
        except AttributeError:
            raise SingularityError ("Bad Singularity. Use 'create' method to "
                                     "create a new Singularity.")
    
    @lazy_attr
    def vars(self):
        """
        Return a list of the variable names of this singularity.

        EXAMPLES::
            
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^2 + y^2 + y*z^3)
            sage: W.vars
            [x, y, z]
            
            sage: R.<X1, X2, X3, X4, X5, X6> = QQ[]
            sage: W = Singularity.create(X4^3*X5 + X2^4*X4 + X5^2*X2)
            sage: W.vars
            [X2, X4, X5]
        
        """
        if self.poly == 0:
            return 0
        try:
            return list(self.poly.variables())
        except AttributeError:
            raise SingularityError ("Bad Singularity. Use 'create' method to "
                                     "create a new Singularity.")

    @lazy_attr
    def monomials(self):
        """
        OUTPUT:
        
        - A list of monomials in this polynomial.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
            sage: W.monomials
            [x^3, x*y*z, y^3, z^3]
            
            sage: W = Singularity.create(x^3*y + y^3)
            sage: W.monomials
            [x^3*y, y^3]
        
        """
        return self.poly.monomials()
    
    def _is_nondegenerate(self):       
        # The nondegeneracy tests is now a composition of 2 tests. If the first test
        # fails, then the second test is used.
        
        # Test 1: Here the dimension of the solution space is checked to see that if
        # it is just 0 (which is the origin)
        # The test does not work if the coefficients are not rational
        # Created by (Julian Tay, Sep 2012)
        
        J = []
        
        try:
            tot_vars = len(self.poly.variables())
            names = [str(var) for var in self.poly.variables()]
            R = PolynomialRing(QQ, tot_vars, list(names)[:tot_vars],
            order=self.term_order)
            
            for var in self.poly.variables():
                J.append(R(self.poly.derivative(var)))
            
            ideal_dim = R.ideal(J).dimension()
            
            if ideal_dim == 0:
                return True
            else:
                raise SingularityError( "Polynomial is not non-degenerate"  )          
            
        except TypeError:
            pass        
        
        # Test 2: Here, a sage solve method is employed to find the actual solutions.
        # It is possible that sage would not be able to solve the equations and would
        # return back the same set of solutions. There is a method that would check
        # that and return an error if solve() fails.
        # Created by (Drew Johnson, 2010 - 2011)
        # Modified by (Julian Tay, Sep 2012)
        
        for var in self.poly.variables():
            J.append(self.poly.derivative(var))
        # Convert things to expressions using SR() so we can solve equations.
        # Before using SR(), expressions and variables are converted to strings
        # to prevent confusing in parent rings (Julian Tay, Aug 2012; checked by
        # Scott Mancuso)
        equations = [SR(str(expr)) == 0 for expr in J]
        variables = [SR(str(t)) for t in self.poly.variables()]
        right_answer = [t == SR(0) for t in variables]
        
        if len(variables) == 1:
            # Outwit sage's dumb conversions when solving for only one variable.
            variables = variables[0]
            right_answer = [variables == SR(0)]
        
        answer = solve(equations, variables)
        
        # More stuff to get around sage's one variable conventions.
        if len(right_answer) == 1:
            answer = [answer]
        
        # Having no solutions means that the polynomial is not non-degenerate
        if answer ==[]:
            raise SingularityError( "Polynomial is not non-degenerate")
              
        # Sometimes solve returns a list, other times it returns a list within a list
        try:
            set_answer = set(answer[0])
        except:
            set_answer = set(answer)
        
        # Catches errors if sage does not solve anything
        if set_answer == set(equations):
            raise SageSolveError( "Sage did not solve for singularities")
        
        # Wrong number of solutions certainly won't match.
        if (len(answer[0]) != len(right_answer)):
            raise SingularityError( "Polynomial is not non-degenerate")
        for u in zip(answer[0], right_answer):
            if u[0] != u[1]:
                raise SingularityError( "Polynomial is not non-degenerate")
        return True
    
    def _is_likely_nondegenerate(self):
        """
        Determine whether a generic polynomial with this weight system is
        non-degenerate. This implements the methods discussed in [HK]_. This
        method raises an exception if the tests fail and returns ``True`` if
        they pass.
        
        .. NOTE::
        
            This method does not guarantee that ``self`` is non-degenerate. It
            is possible that, due to the specific coefficients used, ``self`` is
            degenerate even though a generic polynomial isn't. To ensure
            non-degeneracy, the method :meth:`~Singularity._is_nondegenerate`
            should be used. However, if this method raises an error, you are 
            guaranteed that ``self`` is degenerate.
        
        .. NOTE::
        
            The naming conventions followed here are those from [HK]_.
        
        EXAMPLES::
        
            sage: R.<w, x, y, z> = QQ[]
            sage: W = Singularity.create(y^4*z + w*x*y^2 + x^2*z + z^3 + w^2*x, 
            ...   prove_nondegenerate=False)
            sage: W._is_likely_nondegenerate()
            True
            sage: W = Singularity.create(y^4*z + w*x*y^2 + x^2*z + z^3, 
            ...   prove_nondegenerate=False)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate
            sage: W = Singularity.create(x^3*y + y^4*z + z^6*x + w^73 + 
            ...   w^4*x*y^2*z^2, prove_nondegenerate=False)
            sage: W._is_likely_nondegenerate()
            True
            sage: W = Singularity.create(x^2*y^2 + y^2*z + z^3 + w^2*x^3, 
            ...   prove_nondegenerate=False)
            Traceback (most recent call last):
            ...
            SingularityError: Polynomial is not non-degenerate

        
        AUTHOR:
        
        - Scott Mancuso (April 2013)
        
        """
        # First we must have all weights no greater than 1/2.
        if any([2*a > 1 for a in self.q]):
            raise SingularityError( "Polynomial is not non-degenerate")
        
        n = self.nvariables
        N = set(range(n))
        R = self.matrix.rows()
        all_subsets = Subsets(N)
        
        # Check condition (C1)'
        max_order = (n + 1)//2
        small_subsets = all_subsets.filter(lambda J: 0 < len(J) <= max_order)
        monom_support = [set(a.support()) for a in R]
        
        for J in small_subsets:
            # If there is a monomial in `self` such that all of the indices that
            # aren't in J correspond to variables that have an exponent of 0 in
            # that monomial, then this J satisfies (C1).
            if any([a.issubset(J) for a in monom_support]):
                # This J satisfies the first condition in (C1).
                continue
            
            # Otherwise we need to check the second condition in (C1).
            N_minus_J = N.difference(J)
            all_K = all_subsets.filter(lambda K: len(K) == len(J) and N_minus_J.issuperset(K))
            
            found_K = False
            for K in all_K:
                # As far as we know, this K works.
                found_K = True
                for k in K:
                    Rk_support = [set(a.support()) for a in R if a[k] == 1]
                    for s in Rk_support:
                        s.remove(k)
                    if any([a.issubset(J) for a in Rk_support]):
                        continue
                    # If we get here, then this k doesn't work, so K doesn't
                    # work.
                    found_K = False
                if found_K:
                    break
            if not found_K:
                raise SingularityError( "Polynomial is not non-degenerate")
        
        return True
    
    def get_ring(self, polynomial):       
        """
        OUTPUT:
        
        - A ring trimmed down to the size of the polynomial.
        
        .. TODO::
            
            Doesn't seem to work for :class:`~QSingularity.QSingularity` 
            objects (they don't have a ``term_order`` attribute).
        
        """
        tot_vars = len(polynomial.variables())
        names = [str(var) for var in polynomial.variables()]
        
        # Create a new polynomial ring over the same base as the original but
        # with the correct number of variables.
        ring = PolynomialRing(polynomial.parent().base(), tot_vars, 
                              list(names)[:tot_vars], order = self.term_order)
        return ring
    
    @lazy_attr
    def q(self): 
        """
        OUTPUT:
        
        - A tuple of rational numbers representing the weights needed to give 
          this polynomial a weighted degree of 1.
        
        EXAMPLES::
        
            sage: R.<x, y, z> = QQ[]
            sage: W = Singularity.create(x^2*z + y^4*z + z^3 + x^2*y^2)
            sage: W.q
            (1/3, 1/6, 1/3)
            
            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
            sage: W.q
            (1/3, 1/3, 1/3)
        
        """
        if self.nvariables == 0:
            return []
        A = self.matrix
        k = A.right_kernel()
        if not(len(k.basis()) == 0):
            raise SingularityError( "Weights are not uniquely determined")
        ones = vector([1 for i in range(0, len(self.poly.monomials()))])
        try:
            q = A.solve_right(ones)
        except ValueError:
            raise SingularityError( "Singularity is not quasi-homogeneous")
        return q

    @lazy_attr
    def matrix(self):
        """
        OUTPUT:
        
        - The exponent matrix of this polynomial.
        
        EXAMPLES::
        
            sage: from LGModels import *
            sage: R.<x, y, z, w> = QQ[]
            sage: W = Singularity.create(x^3*y + z^3*w^2 + z^5 + w^5 + y^4 + 
            ...   x^4)
            sage: W.matrix
            [4 0 0 0]
            [3 1 0 0]
            [0 4 0 0]
            [0 0 5 0]
            [0 0 3 2]
            [0 0 0 5]
            
            sage: W = Singularity.create(x^3*y + z^14 + y^7 + z^2*y^6)
            sage: W.matrix
            [ 3  1  0]
            [ 0  7  0]
            [ 0  6  2]
            [ 0  0 14]
        
        """
        if self.nvariables == 0:
            return matrix([[]])
        N = self.nvariables
        M = len(self.poly.monomials())
        m = matrix(QQ, M, N)
        i = 0
        for monom in self.poly.monomials():
            for j in range(0, N):
                m[i, j] = monom.degree(self.poly.variable(j))
            i += 1
        return m
    
    def _matrix_(self):
        """Allows use of the built-in Sage function :func:`matrix`."""
        return self.matrix

    @lazy_attr
    def mu(self):
        """
        OUTPUT:
        
        - A positive integer :math:`\mu` which gives the :math:`\mathbb C`
          dimension of the Milnor ring.
        
        EXAMPLES::
        
            sage: R.<x, y, z, w> = QQ[]
            sage: W = Singularity.create(x^3*y + z^3*w^2 + z^5 + w^5 + y^4 + x^4)
            sage: W.mu
            144

            sage: W = Singularity.create(x^3 + y^3 + z^3 + x*y*z)
            sage: W.mu
            8
            sage: W.milnor_ring
            [1, z, y, x, z^2, y*z, y^2, z^3]
            
        """
        q = self.q
        mu = 1
        N = self.nvariables
        for i in range(0, N):
            mu *= (1/q[i] - 1)
        return mu

    @lazy_attr
    def central_charge(self):
        """
        OUTPUT:
        
        - The central charge :math:`\hat c`.
        
        EXAMPLES::
        
            sage: R.<x, y, z, w> = QQ[]
            sage: W = Singularity.create(x^3*y + z^3*w^2 + z^5 + w^5 + y^4 + x^4)
            sage: W.central_charge
            11/5
            
            sage: W = Singularity.create(x^3*y + z^14 + y^7 + z^2*y^6)
            sage: W.central_charge
            2
        
        """
        charge = 0
        q = self.q
        for q_i in q:
            charge += 1 - 2 * q_i
        return charge


class SingularityError(Exception):
    """
    This exception is raised when the user attempts to create an inadmissible
    :class:`~Singularity.Singularity`.
    
    """
    pass


class SageSolveError(Exception):
    """
    This exception is raised when there is a computation problem with Sage's
    solve method.

    """
    pass


