# <endRing> : End_<k>(<m>)
# Remark :
#   BrauerMorphismOfEndRing(g,h,module);          # not algebra hom
#   BrauerMorphismOfEndRingAsAlgebraHomomorphism; # algebra hom
InstallGlobalFunction("BrauerMorphismOfEndRingAsAlgebraHomomorphism", function(g, h, m)
    local k,br,src,rng,srcAsAlg, ideal,endRing;

    k := m.field;
    br := BrauerMorphismOfEndRing(g,h,m);
    src := Source(br);
    rng := Range(br);
    endRing := MatrixAlgebra(k,m.dimension);
    
    if Dimension(src) = 0 then 
        Error("Dimension of source of Brauer morphism of endring = 0 -----------------\n");
    fi;
    if Dimension(rng) = 0 then 
        Error("Dimension of range of Brauer morphism of endring = 0 -----------------\n");
    fi;

    srcAsAlg := Subalgebra(endRing, Basis(src));# source of <br> as algebra
    ideal := TwoSidedIdeal(srcAsAlg, Basis(Kernel(br)));# Kernel of Brauer morphism as ideal of <srcAsAlg>
    # ideal := Kernel(br);# Kernel of Brauer morphism , as not ideal <srcAsAlg>

    return NaturalHomomorphismByIdeal(srcAsAlg,ideal);
end);


# Let <module1> be a trivial source MTX-module.
#  ( Unnecessarily indecomposable )
#
# Aim 
#   Calc 
#       1. a <q>-invariant basis of <module1> (ここでは<module2> として取り直した)
#       2. the BrauerConstruction of <module1>.
#
# Description --------------------------------
    # Args
    #   <g> : a finite group
    #   <q> : a p-subgroup of <g>
    #   <module1> : a trivial source <g>-module 
    #   <vx> : a vertex p-group of <module1>
    # Return 
    #   A record rec(
    #        basis := basis2,        # <basis2> is a basis of <module2> such that <q>-invariant
    #        module := module2,      # <module2> is isomorphic to <module1> and <module2> has a basis <basis2>
    #        quotient := brQuo,      # <brQuo> is the Brauer quotient of <module2> by a <p>-subgroup <q>
    #        representation := rep2  # <representation> : <g> -> GL( <module2> ) ( determined by a basis <basis2> )
    #    ).
    #
    # Remark :
    #   Unnecessarily <module1> is indecomposable and minimality of <vx>.
    #   But we need <vx> is a p-subgroup of <g>.
#----------------------------------------------
InstallGlobalFunction("InvariantBasisAndBrauerQuotientOfTrivialSourceModule", function( g, q, module1, vx )
    local 
        k,
        dc, summands, t, r, triv, ind,
        resRecord, res, rep, decRes, record,
        isos, iso, decMat, basis2, module2, rep2, res2,
        d, ngq, gens, brQuo;

    k := module1.field;
    ngq := Normalizer(g,q);

    #### 1. a <q>-invariant basis #################
    
        # (i) Mackey decomposition
            dc := DoubleCosets( g, vx, q );
            summands := [];
            for t in dc do
                t := Representative(t);
                r := Intersection( vx^t, q );
                r := GroupWithNotEmptyGeneratorsList( r ); 
                triv := TrivialGModule( r, k );
                ind := InductionOfGModule( q, r, triv ); # indecomposable permutation <q>-module
                Add( summands, ind );
            od;

        # (ii) Restriction decompotision of <module>
            resRecord := RestrictedGModuleWithRepresentation( g, q , module1 ); 
            res := resRecord.module;
            rep := resRecord.representation;

            decRes := MTX.Indecomposition( res );
            Sort( decRes, function( x, y ) return x[2].dimension <= y[2].dimension; end );

            record := SubmultichooseFunction
                        ( summands, List( decRes, x -> x[2] ), MTX.IsomorphismModules );
            if record = fail then 
                Error( "<module1> is not a trivial source module. -------------\n" );
            fi;

        # (iii) Replace basis of <module1>
        # <module1> の basis を <basis2> に取りなおす．
        # <basis2> は <q>-set
        #
        # Remark: 
        # Sort しておいたので，
        # <module2> の basis <basis2> は，<q>のactで fix される元たちが先頭にくるような
        # basis の並びになっている．
            isos := record.values; # isos[i] is an isomorphism <decRes>[i] to <summands>[ record.indices[i] ]
            iso := DiagonalMatrixList( isos, k );  # k<q>-hom
            decMat := Concatenation(List( decRes, x-> x[1] )); # iso (indecomposition of <res>) to <module>

            basis2 := iso^-1 * decMat; # <module1> の 新しい基底で， <q>-setになる．
            module2 := GModuleByMats( List( module1.generators, a -> basis2 * a * basis2^-1 ),  
                            module1.dimension, k );
            rep2 := GroupHomomorphismByFunction( Source(rep), Range(rep), x -> basis2 * (x^rep) * basis2^-1 );
            # res2 := RestrictedGModuleGivenRepresentation( rep2, q, module2 ); 

    #### 2. Brauer quotient of a trivial source module <module2> ##################

        d := Size( Filtered( decRes, x -> x[2].dimension = 1 ) ); # dimention of Brauer quotient of <module> by <q>
        gens := List( GeneratorsOfGroup(ngq), x -> PickUpMatrixBlock( x^rep2, 1, 1, d, d ) );
        if d <> 0 then
            brQuo := GModuleByMats( gens, d, k ); # <ngq>-module
        else 
            brQuo := ZeroGModule( Size(ngq), k );
        fi; 

    
    return rec(
        basis := basis2,        # <basis2> is a basis of <module2> such that <q>-invariant
        module := module2,      # <module2> is isomorphic to <module1> and <module2> has a basis <basis2>
        quotient := brQuo,      # <brQuo> is the Brauer quotient of <module2> by a <p>-subgroup <q>
        representation := rep2  # <representation> : <g> -> GL( <module2> ) ( determined by a basis <basis2> )
    );

end);