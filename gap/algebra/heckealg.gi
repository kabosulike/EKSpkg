# args   a : algebra , e : idempotent in a
# return eae : sub algebra of a
InstallGlobalFunction("IdempotentHeckeSubalgebra", function(a, e)
    return Subalgebra(a, Set(Basis(a) , x-> e*x*e ) );
end);


# <args> = [ <a>, <e> ] or
#          [ <a>, <e>, <f> ]
# If <args> = [ <a>, <e> ], 
# then this function returns the subspace <e><a><e> of <a>.
# Else if <args> = [ <a>, <e>, <f> ], 
# then this function returns the subspace <e><a><f> of <a>.
InstallGlobalFunction("IdempotentHeckeSubspace", function(args...)
    local a, e, f;

    if not Size(args) in [2,3] then
        Error( "Wrong Size(<args>)--------------------------\n");
    fi;
    
    a := args[1];
    e := args[2];
    if not e in a then 
        Error( "Not <e> in <a>. --------------------\n");
    fi;

    if Size(args) = 2 then
        return Subspace(a, Set(Basis(a) , x-> e*x*e ) );
    elif Size(args) = 3 then
        f := args[3];
        if not f in a then 
            Error( "Not <f> in <a>. --------------------\n");
        fi;
        return Subspace(a, Set(Basis(a) , x-> e*x*f ) );
    fi;
    
end);


# <args> = [ <alg>, <e> ] or [ <e>, <alg> ].
#
# <e> is an idempotent in algebra <alg>.
# This function returns a subalgebra <e><alg><e>
#   with small generators.
#
# Remark : 
#    gens を set にしてしまうと，順番が変わってしまう．
#    すると，module の generator との順番が合わなくなる場合がある．
InstallGlobalFunction("IdempotentHeckeAlgebraWithSmallGenerators", function( args... )
    local 
        alg, e,
        g,emb, sub,rem,a,pos,vec, 
        gens; #generators of subalgebra
    
    if IsAlgebra(args[1]) then 
        alg := args[1];
        e := args[2];
    else 
        e := args[1];
        alg := args[2];
    fi;
    # CheckAlgebra( alg );


    if IsFreeMagmaRing(alg) then 
        g := UnderlyingMagma(alg);
        emb := Embedding(g,alg);
        gens := List( GeneratorsOfGroup(g), x -> e * x^emb * e ); 
    else 
        gens := List( GeneratorsOfAlgebra(alg), x -> e * x * e ); 
    fi;
    
    sub := Subalgebra( alg, gens );
    vec := Subspace( alg, List( Basis( alg ), x-> e * x * e ) );

    while Dimension(sub) <> Dimension(vec)  do # <gens> に元を追加して取り直し
        a := Random( alg );
        Add( gens, e * a * e );
        sub := Subalgebra( alg, gens );    
    od;

    return sub;
end);