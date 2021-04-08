# <g> : a finite group
# return 
#  a group <g> with not empty list of generators.
InstallGlobalFunction("GroupWithNotEmptyGeneratorsList", function( g )
    local gens;
    if Size(GeneratorsOfGroup(g)) = 0 then 
        gens := [One(g)];
        return GroupWithGenerators(gens);
    else 
        return g;
    fi;
end);



#   <args> = [ <g1>, <g2>, <h> ] or 
#            [ <g1>, <g2>, <h>, <phi1>, <phi2> ]
#   Where, 
#   <g1>, <g2> : groups
#   <h> : subgroups of <g1> and <g2>
#   <phi1>, <phi2> : group homomorphisms <h> to <g1>, <h> to <g2> respectively
#
# Return 
#   This function returns the diagonal subgroup of <g1>x<g2> 
#           determined by <phi1> and <phi2>.
#   If Size(args) = 3
#   then <phi1>, <phi2> are inclution maps.
#
# Remark : 
#    Unnecessary <phi1> and <phi2> are injective.
InstallGlobalFunction("DiagonalSubgroup", function( args... )
    local g1, g2, h1, h2, h, phi1, phi2,
        dp, emb1, emb2, gens1, gens2, gens;

    # args >>>>>>>>>>>>>>>>
        if not Size(args) in [3,5] then 
            Error( "Wrong Size(args) --------------------------\n");
        fi;

        g1 := args[1];
        g2 := args[2];
        h := args[3];
        if Size(args) = 3 then
            phi1 := GroupHomomorphismByFunction( h, g1, x -> x );
            phi2 := GroupHomomorphismByFunction( h, g2, x -> x );
        elif Size(args) = 5 then
            phi1 := args[4];
            phi2 := args[5];
        fi;
    # <<<<<<<<<<<<<<<<

    dp := DirectProduct( g1, g2 );
    emb1 := Embedding( dp, 1 );
    emb2 := Embedding( dp, 2 );

    gens := List( GeneratorsOfGroup(h), x -> (x^phi1)^emb1 * (x^phi2)^emb2 );

    return Subgroup( dp, gens );
end);

#   <args> = [ <g1>, <g2>, <h1>, <h2> ] or 
#            [ <g1>, <g2>, <h1>, <h2>, <phi1>, <phi2> ]
#   Where, 
#   <g1>, <g2> : groups
#   <h1>, <h2> : subgroups of <g1>, <g2> respectively
#   <phi1>, <phi2> : group homomorphisms <h1> to <g1>, <h2> to <g2> respectively
#
# Return 
#   This function returns a subgroup of <g1>x<g2> 
#           determined by <phi1> and <phi2>.
#   If Size(args) = 4 
#   then <phi1>, <phi2> are inclution maps.
InstallGlobalFunction("DirectProductSubgroup", function( args... )
    local g1, g2, h1, h2, phi1, phi2,
        dp, emb1, emb2, gens1, gens2, gens;

    # args >>>>>>>>>>>>>>>>
        if not Size(args) in [4,6] then 
            Error( "Wrong Size(args) --------------------------\n");
        fi;

        g1 := args[1];
        g2 := args[2];
        h1 := args[3];
        h2 := args[4];
        if Size(args) = 4 then
            phi1 := GroupHomomorphismByFunction( h1, g1, x -> x );
            phi2 := GroupHomomorphismByFunction( h2, g2, x -> x );
        elif Size(args) = 6 then
            phi1 := args[5];
            phi2 := args[6];
        fi;
    # <<<<<<<<<<<<<<<<

    dp := DirectProduct( g1, g2 );
    emb1 := Embedding( dp, 1 );
    emb2 := Embedding( dp, 2 );

    gens1 := List( GeneratorsOfGroup(h1), x -> (x^phi1)^emb1 );
    gens2 := List( GeneratorsOfGroup(h2), x -> (x^phi2)^emb2 );
    gens := Concatenation( gens1, gens2 );

    return Subgroup( dp, gens );
end);

#
    # <prd> : direct product containing g1^emb1 and g2^emb2.
    # return 
    #   subgroup <g> of prd. Where <g> iso direct product <g1>x<g2>
InstallGlobalFunction("EmbeddingSubgroupToDirectProduct", function(prd,g1,g2)
    local gens, emb1, emb2;
    emb1 := Embedding(prd,1);
    emb2 := Embedding(prd,2);

    if not IsSubset( Source(emb1), g1 ) then 
        Error("not IsSubset( Source(emb1), g1 ) -------------------------\n");    
    elif not IsSubset( Source(emb2), g2 ) then 
        Error("not IsSubset( Source(emb2), g2 ) -------------------------\n");    
    fi;
    
    gens := Concatenation(
        List( GeneratorsOfGroup(g1), x-> x^emb1 ),
        List( GeneratorsOfGroup(g2), x-> x^emb2 )
    );
    return Subgroup(prd, gens);
end);

InstallGlobalFunction("ConjugacyClassesSubgroupsOfFixedSubgroup", function(G,Q)
    local ccQ,ccQG,i;
    ccQ:=ConjugacyClassesSubgroups(Q);
    ccQG:=[];
    for i in [1..Length(ccQ)] do
        if ForAll(ccQG,j->not (Representative(ccQ[i]) in j)) then
            Add(ccQG,ConjugacyClassSubgroups(G,Representative(ccQ[i])));
        fi; 
    od;
    return ccQG;
end);

InstallGlobalFunction("ModularConjugacyClassesSubgroups", function(G,p)
    local Ps;
    Ps:=SylowSubgroup(G,p);
    return ConjugacyClassesSubgroupsOfFixedSubgroup(G,Ps);
end);

InstallGlobalFunction("AllSemidirectProducts", function(n,h)
    return AllSemidirectProductsWithHomomorphisms(n,h).semidirects;
end);

InstallGlobalFunction("ConjugateActionSemidirectProduct", function( g, n, q )
    local cgq, pi, e, preImgs, reps, imgs, alpha;
    
    cgq := Centralizer(g,q);
    pi := NaturalHomomorphismByNormalSubgroup( n, cgq );
    e := n/cgq;
    preImgs := List( GeneratorsOfGroup(e), x -> PreImagesElm( pi, x ) );
    reps := List( preImgs, Representative );
    imgs := List( reps, x -> GroupHomomorphismByFunction( q, q , u -> u^x  ) );
    alpha := GroupHomomorphismByImages( e, AutomorphismGroup(q), imgs );

    return SemidirectProduct( e, alpha, q );
end);

# <g> = <n><k> : semidirect product 
# <n> : normal subgroup of <g>,  <k> : subgroup of Aut(n)
# return 
#   true iff <k> act freely on <n>-1. 
InstallGlobalFunction("IsFrobeniusGroupWithRepresentativeRightCosets", function(n,rc,q,g)
    local omega, list ;
    omega := Filtered(q,x->x<>One(q));
    list := Concatenation(List( omega , a-> List(rc , b -> [a,b] ) ));

    return ForAll(list, function(ab)
        local a,b;
        a := ab[1];
        b := ab[2];
        return a^b <> a or b=One(g);
    end);
end);

InstallGlobalFunction("IsFrobeniusGroupWithParentGroup", function(g,n,q)
    local rc;

    if not IsSubgroup(g,n) then 
        Error("not IsSubgroup(g,n) ----------------------\n");
    fi;
    if not IsSubgroup(n,q) then 
        Error("not IsSubgroup(g,n) ----------------------\n");
    fi;

    if not IsNormal(g,n) then 
        Error("not IsNormal(g,n) \n----------------------");
    fi;
    
    rc := List(RightCosets(g,n),Representative);
    return IsFrobeniusGroupWithRepresentativeRightCosets(n,rc,q,g);
end);


InstallGlobalFunction("IsFrobeniusGroup", function(args...)
    local g,n,rc,q;

    if Size(args) = 3 then
        if IsGroup(args[1]) and IsGroup(args[2]) and IsGroup(args[3]) then 
            g := args[1];
            n := args[2];
            q := args[3];
            return IsFrobeniusGroupWithParentGroup(g,n,q);
        fi;
    elif Size(args) = 4 then 
        if IsGroup(args[1]) and not IsGroup(args[2]) and IsGroup(args[3]) then 
            n := args[1];
            rc := args[2];
            q := args[3];
            g := args[4];
            return IsFrobeniusGroupWithRepresentativeRightCosets(n,rc,q,g);
        fi;
    fi;

    Error("<args> is not supported type. \n--------------------------");
end);


InstallGlobalFunction("AllSubgroupsNonEmptyGenerators", function(g)
    local subs, i ;

    # Do not know the first element of AllSubgroups(g) is trivial group.
    subs := AllSubgroups(g);
    for i in [1..Size(subs)] do
        if Order(subs[i]) = 1 then 
            subs[i] := Subgroup(g, [One(g)]);
            break;
        fi;

    od;
    return subs;
end);
# Debug >>>>>>>>>>>>>>>>>>>>>> 
# g := SmallGroup(18,1);
# subs1 := AllSubgroups(g);
# subs2 := AllSubgroupsNonEmptyGenerators(g);
# Print(List(subs1,GeneratorsOfGroup),"\n");
# Print(List(subs2,GeneratorsOfGroup),"\n");
# end Debug <<<<<<<<<<<<<<<<<<< 


InstallGlobalFunction("ModularConjugacyClassesSubgroupsNonEmptyGenerators", function(g,p)
    local ccs, i ;
    ccs := ModularConjugacyClassesSubgroups(g,p);

    # Do not know the first element of <ccs> is the class containing trivial group.
    for i in [1..Size(ccs)] do
        if Order(Representative(ccs[i])) = 1 then 
            ccs[i] := Subgroup(g, [One(g)])^g;
            break;
        fi;
    od;
    return ccs;
end);


# =========================================================================
# arg 
# <x> : a group element
# <p> ; a prime number
# return 
# <p> part と <p>-regular part に <x> を分解した結果がレコードで帰ってくる。
# 
InstallGlobalFunction("PDecompositionOfGroupElement", function(x,p) 
    local ord, ordppart, ordpregpart,coef;
    if not IsPrimeInt(p) then
        Error("p is not a prime");
    fi;
        ord:=Order(x);
        ordppart:=p^PadicValuation(ord,p);
        ordpregpart:=ord/ordppart;
        coef:=GcdRepresentation(ordppart,ordpregpart);
    return rec(p_regular_part:=x^(ordppart*coef[1]),p_part:=x^(ordpregpart*coef[2]));
end);