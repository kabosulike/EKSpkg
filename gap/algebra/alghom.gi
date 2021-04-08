InstallGlobalFunction("InclusionAlgebraHomomorphism", function( sub, alg )
    return AlgebraHomomorphismByImages( sub, alg, GeneratorsOfAlgebra(sub), GeneratorsOfAlgebra(sub) );
end);


InstallGlobalFunction("IdentityHomomorphismOfAlgebra", function(alg)
    return AlgebraHomomorphismByImages(Source(alg),Range(alg),GeneratorsOfAlgebra(alg),GeneratorsOfAlgebra(alg));
end);


InstallGlobalFunction("QuotientAlgebraHomomorphismByIdeal", function(alg,ideal)
    if Dimension(alg) = 0 then 
        Error("Dimension(alg) = 0 -------------------------\n");
    fi;        

    # if Dimension(ideal) = 0 then 
    #     return IdentityHomomorphismOfAlgebra(alg);
    # else 
        return NaturalHomomorphismByIdeal(alg, ideal);
    # fi;
end);


InstallGlobalFunction("QuotientAlgebraHomomorphismOfTopOfAlgebra", function(alg)
    if Dimension(alg) = 0 then 
        Error("Dimension(alg) = 0 -------------------------\n");
    fi;        

    return QuotientAlgebraHomomorphismByIdeal(alg, RadicalOfAlgebra(alg));    
end);

