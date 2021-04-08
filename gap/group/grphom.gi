# GroupHomomorphismDirectProduct := function(g1,g2, h1,h2, alp, bet )
#     local prdS, prdR, embR1, embR2, imgs;
    
#     prdS := DirectProduct(g1, g2);
#     prdR := DirectProduct(h1, h2);
#     # embS1 := Embedding(prdS, 1);
#     # embS2 := Embedding(prdS, 2);
#     embR1 := Embedding(prdR, 1);
#     embR2 := Embedding(prdR, 2);
#     imgs := Concatenation(
#         List(GeneratorsOfGroup(g1), x->(x^alp)^embR1),
#         List(GeneratorsOfGroup(g2), y->(y^bet)^embR2)
#     );
#     return GroupHomomorphismByImages(prdS, prdR, imgs );
# end;

InstallGlobalFunction("GroupHomomorphismDirectProduct", function(parent, g1,g2, h1,h2, alp, bet )
    local prdS, prdR, embP1, embP2, imgs;
    
    embP1 := Embedding(parent,1);
    embP2 := Embedding(parent,2);
    prdS := EmbeddingSubgroupToDirectProduct( parent, g1, g2 );
    prdR := EmbeddingSubgroupToDirectProduct( parent, h1, h2 );
    # alp_ := GroupHomomorphismByImages( parent, parent, List(GeneratorsOfGroup(g1),x->(x^alp)^embP1) );
    # bet_ := GroupHomomorphismByImages( parent, parent, List(GeneratorsOfGroup(g2),y->(y^bet)^embP2) );
    imgs := Concatenation(
        List(GeneratorsOfGroup(g1), x->(x^alp)^embP1),
        List(GeneratorsOfGroup(g2), y->(y^bet)^embP2)
    );
    return GroupHomomorphismByImages(prdS, prdR, imgs ); # prdS , prdR are subgroup of <parent>.
end);

InstallGlobalFunction("InclusionGroupHomomorphism", function(h,g)
    if not IsSubgroup(g,h) then 
        Error("not IsSubgroup(g,h) ----------------------------\n ");
    fi;
    return GroupHomomorphismByFunction(h,g,x->x);
end);

InstallGlobalFunction("AllInjectiveHomomorphisms", function(g,h)
    local homs;
    homs := AllHomomorphisms(g,h);
    return Filtered(homs, IsInjective);
end);

InstallGlobalFunction("AllSurjectiveHomomorphisms", function(g,h)
    local homs;
    homs := AllHomomorphisms(g,h);
    return Filtered(homs, IsSurjective);
end);

InstallGlobalFunction("AllInjectiveHomomorphismClasses", function(g,h)
    local homs;
    homs := AllHomomorphismClasses(g,h);
    return Filtered(homs, IsInjective);
end);

InstallGlobalFunction("AllSurjectiveHomomorphismClasses", function(g,h)
    local homs;
    homs := AllHomomorphismClasses(g,h);
    return Filtered(homs, IsSurjective);
end);


InstallGlobalFunction("ShowMappingGenerators", function(homs)
    local src, gens, phi;

    for phi in homs do
        src := Source(phi);
        gens := GeneratorsOfGroup(src);

        PrintList( gens );
        Print( " -> " );
        PrintList( List( gens, x-> x^phi) , true);
    od;
end);



# -----------------------------------------------------------------------------
# <n> , <h> : finite groups 
# return 
#   record 
#        semidirects : list of representative of the isomorphic classes semidirect product n:h
#        homs        : list of hom : h -> Aut(n)
# -------------------
InstallGlobalFunction("AllSemidirectProductsWithHomomorphisms", function(n,h)
    local aut, list, semidirects, homs, classes, reps;
    aut := AutomorphismGroup(n);
    list := List( AllHomomorphisms( h , aut ) , alpha -> [SemidirectProduct(h,alpha,n), alpha ] );
    # list := List( AllHomomorphismClasses( h , aut ) , alpha -> [SemidirectProduct(h,alpha,n), alpha ] ); # 合ってるか不明
    classes := Classification( list, function(g,h) return IsomorphismGroups(g[1],h[1]) <> fail; end ); # first components are groups, second components are group homs.
    reps := List( classes, Representative );

    semidirects := List( reps, x->x[1] );
    homs        := List( reps, x->x[2] );
    return rec( 
        semidirects := semidirects, 
        homs := homs 
    );
end);


InstallGlobalFunction("DiagonalSubgroupEmbedding", function( g, h, d )
    local gh, emb1, emb2, gens, imgs;
    
    gh := DirectProduct( g, h );
    emb1 := Embedding( gh, 1 );
    emb2 := Embedding( gh, 2 );

    gens := GeneratorsOfGroup(d);
    imgs := List( gens, x -> x^emb1 * x^emb2 );
    return GroupHomomorphismByImages( d, gh, gens, imgs );
end);