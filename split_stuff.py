def split_poly_old( poly ):
    """
    Write a polynomial as the sum of a maximal number of polynomials with independent variables.

    INPUT:
    
    - ``poly`` -- A Sage polynomial
    
    OUTPUT:
    
    A dictionary whose values are the desired polynomials and whose keys are the variables used in those polynomials
    
    .. NOTE::
        This function is not used for anything in this file, but I wrote it and didn't want to get rid of it.
    """
    try:
        monoms = poly.monomials()
    except AttributeError:
        raise Exception, "Input must be a member of a multivariate polynomial ring."
    
    ########CAN THIS EVER HAPPEN?##########################
    if monoms == []:
        raise Exception, "You can't use an empty polynomial"
    
    poly_dict = {}
    
    for monom in monoms:
        new_key = frozenset( monom.variables() )
        if new_key in poly_dict.keys():
            poly_dict[ new_key ] += monom       #if these exact variables were already a key, add the monomial to this key's list
        else:
            poly_dict[ new_key ] = monom
            other_keys = poly_dict.keys()       #for whatever reason other_keys = poly_dict.keys().remove( new_key ) WILL NOT WORK so don't try it.
            other_keys.remove( new_key )
            for other_key in other_keys:
                if not new_key.isdisjoint( other_key ): 
                    new_vals =  poly_dict.pop( new_key )    #merge the keys and their corresponding values
                    other_vals =  poly_dict.pop( other_key )
                    poly_dict[ new_key.union( other_key ) ] = new_vals + other_vals #end merge
                    
                    new_key = new_key.union( other_key )
    
    #make a new dictionary with keys equal sets of the indexes of the variables; values are the sub-poly using these variables
    new_dict = {}
    for key in poly_dict.keys():
        new_key = frozenset( [poly.variables().index(x) for x in key] )
        new_dict[ new_key ] = poly_dict[ key ]
        
    poly_dict = new_dict
    
    return poly_dict

def split_poly( poly ):
    """
    Write a polynomial as the sum of a maximal number of polynomials with independent variables.

    INPUT:
    
    - ``poly`` -- A Sage polynomial
    
    OUTPUT:
    
    A list of frozensets of indexes, where indexes correspond to variables that make a independent sub-polynomial
    
    .. NOTE::
        This function is used by split_state_space. Its output isn't good for much else.
    """
    try:
        monoms = poly.monomials()
    except AttributeError:
        raise Exception, "Input must be a member of a multivariate polynomial ring."
    
    ########CAN THIS EVER HAPPEN?##########################
    if monoms == []:
        raise Exception, "You can't use an empty polynomial"
    
    monoms = [ [poly.variables().index(i) for i in m.variables() ] for m in monoms ]
    poly_list = []
    
    for monom in monoms:
        new_poly = frozenset( monom )
        if not new_poly in poly_list:
            poly_list.append( new_poly )
            other_polys = [ p for p in poly_list]
            other_polys.remove( new_poly )
            for other_poly in other_polys:
                if not new_poly.isdisjoint( other_poly ): 
                    poly_list.remove( new_poly )    #merge the sets
                    poly_list.remove( other_poly )
                    new_poly = new_poly.union( other_poly )
                    poly_list.append( new_poly ) #end merge
                    
    return poly_list
    
def split_state_space( sym_group ):    
    """
    Break a SymmetryGroup into a cross product of SymmetryGroups so that the sum of the polynomials for these groups is the original Singularity associated with the SymmetryGroup.
    
    INPUT:
    
    - ``sym_group`` -- A SymmetryGroup instance
    
    OUTPUT:
    
    A list of SymmetryGroup-Singularity pairs
    
    .. NOTE::
        This function works for any sort of group now.
        
        Note that if the group is contained in SLn or contains J, the direct summands will be as well. 
        Also, if the original polynomial satisfies all hypotheses necessary for FJRW ring construction, the smaller polynomial summands will too.
    """
    
    singularity = sym_group.poly
    subgroup_indexes = split_group( sym_group )
    index_list = split_poly(singularity.poly)
    
    #print subgroup_indexes
    
    #find the smallest decomposition that respects both the split poly and the split group
    for indexes in subgroup_indexes:
        new_indexes = frozenset( indexes )
        if not (new_indexes in index_list):
            index_list.append( new_indexes )
            other_index_list = [ p for p in index_list]
            other_index_list.remove( new_indexes )
            for other_indexes in other_index_list:
                if not new_indexes.isdisjoint( other_indexes ): 
                    index_list.remove( new_indexes )    #merge the sets
                    index_list.remove( other_indexes )
                    new_indexes = new_indexes.union( other_indexes )
                    index_list.append( new_indexes ) #end merge
    
    group_list = []
    poly_list = []
    poly_vars = singularity.poly.variables()
    
    
    for indexes in index_list:  #loop once through for every subgroup/subpoly we found
        #make list of subgroups
        subgroup_gens = []
        for gen in sym_group.gens:
            subgroup_gens.append( [ gen.value[i] for i in indexes ] )
        group_list.append( subgroup_gens )  
        
        #make list of summed polys
        new_poly = 0
        for monom in singularity.poly.monomials():
            for i in indexes:
                if poly_vars[i] in monom.variables():
                    new_poly += monom
                    break
        poly_list.append( new_poly )
    
    
    poly_list = [ Singularity.create( poly ) for poly in poly_list ]
    group_list = [ SymmetryGroup( poly, gens ) for (poly, gens) in zip( poly_list, group_list ) ]
    
    print [ (W.poly, G.gens) for (W, G) in zip( poly_list, group_list )]
    return [ (W, G) for (W, G) in zip( poly_list, group_list )]
    #return group_list
    
    #tensor_product = [FJRWRing(g, printBasis = False) for g in group_list]
    #for fjrw in tensor_product:
    #    fjrw.print_summary()
    #    print ""
    #return tensor_product
    
    
def split_group( G ):
    """
    Write a SymmetryGroup as a cartesian product of a maximal number of groups
    
    INPUT:
    
    - ``G`` -- A SymmetryGroup instance
    
    OUTPUT:
    
    A list of index-lists, each index-list being a list of indexes corresponding to the coordinates of the original group that form a subgroup, direct sum of which is original group.
    
    .. NOTE::
        This function is called by split_state_space and probably doesn't make sense for anything else.
    """
    
    valid_indexes = set(xrange(0, G.length))  #valid_indexes is a list of coordinates of G that have not yet been found to be part of a subgroup
    direct_sum = []                     #a list of the subgroups G is a direct sum of
    
    for subgroup_length in xrange(1, (G.length + 1)// 2 + 1 ):  #I want to use as many as half my coordinates (rounded up) in a candidate subgroup
        poss_indexes = Combinations( valid_indexes, subgroup_length).list()
        for indexes in poss_indexes:
            if is_subgroup( indexes, G ):   #SUPER WARNING!!! I think I don't need to say "and valid_indexes.issuperset( indexes )"- I think just checking for subgroups will catch this, but maybe adding this would be faster, and anyway I'm not sure.
                direct_sum.append( indexes )    
                valid_indexes = valid_indexes.difference( indexes )
    
    
    if list(valid_indexes) != []:
        direct_sum.append( list(valid_indexes) )  #add on whatever was left of the group.
    
    return direct_sum
        
    
def get_possible_indexes( length, valid_indexes ):
    """
    get a list of index-lists, where each index-list is of lenght 'length' and only uses indexes found in valid_indexes. 
    for implementation 2, use poly_dict for information about split polynomial.
    There are two ways to implement this function. 
    1)  return a list of all ways to choose 'length' indexes out of all the possible coordinates in G.length
    2)  return a list of all the ways to sum sub-polys into polys using 'length' variables
    
    .. NOTE::
        This function isn't used for anything and should be deleted.
    """
    return Combinations( valid_indexes, length).list()
    
    
    
    
    
def is_subgroup( indexes, G):
    """
    check if (the complement of) indexes form a directly subtractable subgroup of G
    """
    
    gens = [ list(g.value) for g in G.gens]
    elems = [ list(e.value) for e in G ]
    
    sub_gens = gens
    
    for gen in sub_gens:
        for i in indexes:
            gen[i] = 0          #if this set of indexes forms a subgroup, its complement will as well; this is easier to code
        if gen not in elems:
            return False        #if a restricted generator is not an element of the group, this was not really a subgroup.
            
    return True                 #however, if all restricted gens are group elements, this is a subgroup
        