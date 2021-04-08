# Return a vector <v> on <k> dimension <dim> such that 
#   [0,0,...,0,1,0,...0].
# (<index>-th element is one, else are zero.)
InstallGlobalFunction("CanonicalVector", function(dim, index, k)
    local v;
    v := NullMat(1,dim,k)[1]; # vector
    v[index] := One(k);
    return v;
end);


InstallGlobalFunction("NormOfVector", function( vec )
    return Sqrt(Sum( List(vec, x -> x^2 ) ));
end);


# <a> = vector or (list of vector).
InstallGlobalFunction("Normalization", function( a )
    if IsVector(a) and ( not IsMatrix(a) ) then 
        return NormOfVector(a)^-1 * a;
    elif IsMatrix(a) and a <> [] and IsVector(a[1]) then 
        return List( a, v ->  NormOfVector(v)^-1 * v );
    else 
        return fail;
    fi;
end);


# <list> is a list of vectors which elements in a ring <ring>.
# This function returns 
#   true (if <list> is orghogonal vectors) or
#   false (else).
InstallGlobalFunction("IsOrthogonal", function( list, ring )
    local i,j, v,w;

    for i in [1..Size(list)] do
        for j in [i+1..Size(list)] do
            v := list[i];
            w := list[j];
            if v*w <> Zero(ring) then 
                return false;
            fi;
        od;
    od;
    return true;
end);


# <a> is a list of vector.
# This function returns the list of vector 
#   determined by Gram-Schmidt algorithm.
# But this function does not normalization.
InstallGlobalFunction("GramSchmidtOrthogonal", function(a)
    local b, m , am, bm, tmp;
    
    b := [];
    for m in [1..Size(a)] do
        tmp := List( [1..m-1] , i -> ((a[m]*b[i])/(b[i]*b[i])) * b[i] );
        b[m] := a[m] - Sum( tmp );
    od;

    return b;
end);


InstallGlobalFunction("GramSchmidtOrthonormalization", function(a)
    local gs;
    gs := GramSchmidtOrthogonal(a);
    return List( gs, Normalization );
end);