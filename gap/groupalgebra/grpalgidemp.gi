# Args
#   <pd> : a primitive decomposition record
#           (For example, pd := PrimitiveDecompositionInFixedElementsSubalgebra( One(kg), q, kg); )
#   <q> : a <p>-subgroup of <g>
#   <kg> : the group algebra of <g> with coefficients in <k>
# Return the local part indices list <indices>.
InstallGlobalFunction("LocalPartIndicesOfPrimitiveDecomposition", function( pd, q, kg )
    local br, indices;
    
    br := BrauerMorphismOfGroupAlgebra( q, kg );
    indices := Filtered( [1..Size(pd.idempotents)], i -> pd.idempotents[i]^br <> Zero(kg) );
    pd.localIndices := indices;

    return indices;
end);


# Args
#   <pd> : a primitive decomposition record
#           (For example, pd := PrimitiveDecompositionInFixedElementsSubalgebra( One(kg), q, kg); )
#   <q> : a <p>-subgroup of <g>
#   <kg> : the group algebra of <g> with coefficients in <k>
# Return an indices list <reps>. Where <reps> is a representatives local part indices.
# This function adds  
#   <pd.localIndices>,
#   <pd.classes>,
#   <pd.mlties>
#   <pd.isLocalList> # <pd.isLocalList>[i] = true (iff pd.classes[i] is corresponding local point )
#   <pd.localReps>,
#   <pd.nonLocalReps>
InstallGlobalFunction("LocalPartIndicesRepresentativesOfPrimitiveDecomposition", function( pd, q, kg )
    local indices, g, br, classes, localReps, nonLocalReps, isLocalList, i, c, cap, ind;

    if not IsBound( pd.localIndices ) then 
    LocalPartIndicesOfPrimitiveDecomposition( pd, q, kg ); # local part indices
    fi;
    indices := pd.localIndices;
    
    g := UnderlyingMagma( kg );
    br := BrauerMorphismOfGroupAlgebra( g, q, kg );

    # <pd.classes>, 
    # <pd.mlties>
        if IsBound(pd.classes) then 
            classes := pd.classes;
        else 
            IsomorphicClassification( pd );
            classes := pd.classes;
        fi;
        pd.mlties := List( classes, c -> Size(c) );
    
    # <pd.localReps>,
    # <pd.nonLocalReps>,
    # <pd.isLocalList>
        localReps := [];    #     local representatives
        nonLocalReps := []; # not local representatives
        isLocalList := [];  
        for i in [1..Size(classes)] do 
            c := classes[i];    # c is an indices class
            cap := Intersection(c, indices);
            if cap <> [] then 
                ind := Representative( cap );
                Add( localReps, ind );

                Add( isLocalList, true );
            else 
                ind := Representative( c );
                Add( nonLocalReps, ind );

                Add( isLocalList, false );            
            fi;
        od;
        pd.localReps    :=    localReps;
        pd.nonLocalReps := nonLocalReps;
        pd.isLocalList  := isLocalList;

    return localReps;
end);


# Args 
#   <e> : an idempotent in <kg>^<q>
#   <q> : a <p>-subgroup of <g>
#   <kg> : the group algebra
# Return a primitive decomposition record <pd> containing <.localIndices>.
InstallGlobalFunction("PrimitiveDecompositionInFixedElementsSubalgebraAddLocalPartIndices", function( e, q, kg )
    local pd;
    
    pd := PrimitiveDecompositionInFixedElementsSubalgebra( e, q, kg );
    LocalPartIndicesOfPrimitiveDecomposition( pd, q, kg );

    return pd;
end);


InstallGlobalFunction("LocalPartOfIdempotentsWithModules", function(e,q,kg)
# e: an idempotent 
# q: a p-subgroup of g 
local r, idemps, br, k, g, indices, i;
    k := LeftActingDomain(kg);
    g := UnderlyingMagma(kg);
    r := PrimitiveDecompositionInFixedElementsSubalgebra(e, q, kg); # record
    idemps:= r.idempotents;
    br := BrauerMorphismOfGroupAlgebra(g,q,kg);
    indices:= [];
    for i in [1..Length(idemps)] do
        if idemps[i]^br <> Zero(kg) then # By construction of <idemps>, always e*idemps[i]* <> zero.
        # if e*idemps[i]*e <> Zero(kg) and idemps[i]^br <> Zero(kg) then 
            Add(indices, i);
        fi;
    od;
    return rec(
        idempotents:= r.idempotents{indices},
        modules:= List(r.indecomposition{indices}, x->x[2]),
        indices:= indices,
        indecomposition:= r.indecomposition
    );
end);


InstallGlobalFunction("LocalPartOfIdempotents", function(e,q,kg)
    return LocalPartOfIdempotentsWithModules(e,q,kg).idempotents;
end);


# args:
#   args[1] = <b> : a block idempotent of <kg>
#   args[2] = <kg>: the group algebra of <g> with coefficients in <k>
#   (args[3] = <d> : a defect group of <b>) : 省略可
# or
#   args[1] = <b> : a block idempotent of <kg>
#   args[2] = <d> : a defect group of <b>
#   args[3] = <kg>: the group algebra of <g> with coefficients in <k>
# or 
#   args[1] = [ [b,kg,d] ] or [ [b,d,kg] ]
#
# return 
#   Record of local parts of block idempotent <b>.
#   i.e. source idempotents which appear decomposition of <b> 
InstallGlobalFunction("SourceIdempotentDecomposition", function(args...)
    local b,kg,d;

    if IsList(args[1]) then 
        args := args[1];
    fi;
    
    if Size(args) = 2 then 
        b := args[1];
        kg := args[2];
        d := DefectGroupOfBlockOfGroupAlgebra(b,kg);
    elif Size(args) = 3 then
        if IsGroup(args[3]) then 
            b := args[1];
            kg := args[2];
            d := args[3];
        elif IsGroup(args[2]) then 
            b := args[1];
            d := args[2];
            kg := args[3];
        fi;
    else 
        Error("Wrong size of args --------------\n");
    fi;

    # if IsConjugacyClassGroupRep(d) then # d = d0^g ( some defect group d0 )
    #     d := Representative(d);
    # fi;

    return LocalPartOfIdempotentsWithModules(b,d,kg);
    # return _SourceIdempotentsWithModules(b,d,kg);
end);


InstallGlobalFunction("SourceIdempotents", function(args...)
    return SourceIdempotentsWithModules(args).idempotents;
end);


InstallGlobalFunction("SourceIdempotent", function(args...)
    return Representative(SourceIdempotentsWithModules(args).idempotents);
end);