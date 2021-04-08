# 群環のsubalgebra<A>を<h>加群としてみたときのGModuleを返す
# InstallGlobalFunction("GroupAlgebraAsGModule", function(h, A)
#     return GBimoduleByRegularAction(TrivialSubgroup(h), h, A, TopParent(A));
# end);


CartanMatrixOfGroupAlgebra@ := function( irrs, g, k )
    local 
        cf,
        cartan,
        # irrs,
        PIM, pim, sortedPIM,
        s
    ;

    # irrs := IrreducibleModules(g,k,Order(g))[2];
    PIM := MTX.HomogeneousComponents(RegularModule(g,k)[2]);
    PIM := List( [1..Size(PIM)] , i->PIM[i].component[2]);
    cartan := [];

    # We construct sortedPIM satisfying
    #    sortedPIM[i] iso irrs[i].
    sortedPIM := [];
    for s in irrs do
        for pim in PIM do 
            # if MTX.IsomorphismModules(TopOfGModule(pim) ,s) <> fail then  # If immutable, then error.
            if IsIsomorphicGModules(TopOfGModule(pim) ,s) then 
                Add(sortedPIM, pim);
                break;
            fi;
        od;
    od;
    
    for pim in sortedPIM do 
        cf := FixedIrreduciblesCompositionFactorsMultiplicity( pim, irrs );
        Add( cartan , cf );
    od;

    return cartan;
end;


# args
#  [ g,k ] or
#  [ irrs, g, k ]
InstallGlobalFunction("CartanMatrixOfGroupAlgebra", function(args...)
    local irrs, g, k ;
    if Size(args) = 2 then 
        g := args[1];
        k := args[2];
        irrs := IrreducibleModules(g,k,Order(g))[2];
    elif Size(args) = 3 then 
        irrs := args[1];
        g := args[2];
        k := args[3];
    fi;
    
    return CartanMatrixOfGroupAlgebra@(irrs, g, k);
end);


InstallGlobalFunction("ClassificationIrreduciblesSameBlock", function(irrs, cartan)
    local lyingSameblock, binaryRel, i,j;
    
    binaryRel := function(i,j)
        if cartan[i][j] >= 1 then 
            return true;
        else
            return false;
        fi; 
    end;
    
    lyingSameblock := ClassificationByBinaryRelation(List([1..Size(irrs)]), binaryRel); # example : [[1,2,3],[4]]
    return  List( [1..Size(lyingSameblock)] , n ->
               List(lyingSameblock[n] , i->irrs[i] ) 
            );

end);


# =========================================================================
# return : if <module> has lying <blockIdem> part then true , else return false.
InstallGlobalFunction("IsModuleHasLyingBlockPart", function( blockIdem, module , g )
    return DimensionOfDirectSummandOfGModule( blockIdem, module , g ) <> 0;
end);


# return : if <module> lying a block <blockIdem> then true, else return false.
InstallGlobalFunction("IsModuleLyingBlock", function( blockIdem, module , g )
    return DimensionOfDirectSummandOfGModule( blockIdem, module , g ) = module.dimension;
end);
