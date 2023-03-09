####################################################################
#% Description of interior G-algebra

	# A record <intA> is called interior G-algebra 
	# if <intA> has components .algebra, .generators (, .one ) . 
	# Where, 
	#  intA.algebra is an algebra,
	#  intA.generators is the image a structural map of a generators of G,
	#  intA.one is the one of intA.algebra.
####################################################################



# Args
# args = [ module, e, h, kg, ekge ] or
#        [ module, e, h, kg ]
# 
# <module> : <g>-module
# <ekge> : subalgebra <e><kg><e> of <kg>. <ekge> is an interior <h>-algebra.
# <e> : an idempotent in fixed elements subalgebra <kg>^<h>
# <h> : a subgroup of <g>
# <kg> : the group algebra of <g> with coefficients in <k>
# Return 
#  A record rec( module, restriction ).
#   Where 
#       rec.module is a <ekge>-module <module>*<e>.
#       rec.restriction is a restricted module <module>*<e> to <h>
InstallGlobalFunction("IdempotentHeckeGroupRingModule", function( args... )
    local k, g, rep, emat, dim, indices, vs, genes, module_e, res, emb, 
        ekge, module, e, h, kg;

    if not Size(args) in [5,4] then
        Error( "wrong number of arguments --------------------------\n");
    fi;
    
    module := args[1];
    e := args[2];
    h := args[3];
    kg := args[4];
    if Size(args) = 5 then
        ekge := args[5];
    elif Size(args) = 4  then
        ekge := IdempotentHeckeAlgebraWithSmallGenerators( e, kg );
    fi;
    
    k := module.field;
    g := UnderlyingMagma(kg);
    rep := MatrixRepresentationByGModule( g, module );
    if rep = fail then 
        return rec(
            module := ZeroGModule( Size(GeneratorsOfAlgebra(ekge)), k ),
            restriction := ZeroGModule( Size(GeneratorsOfGroup(h)), k )  # res of <module_e> , <ekge> to <kh>
        );
    fi;
    emb := Embedding(g,kg);

    #  -- Create <module_e> = <module> * (<e>)^<rep>  --
    emat := MapstoLinearExtensionOfGroupHomomorphism( rep, e ); # matrix of e
    dim := RankMat( emat );
    indices := LinearIndependentRows( emat );
    if indices = [] then 
        return rec(
            module := ZeroGModule( Size(GeneratorsOfAlgebra(ekge)), k ),
            restriction := ZeroGModule( Size(GeneratorsOfGroup(h)), k )  # res of <module_e> , <ekge> to <kh>
        );
    fi;
    vs := VectorSpace( k, emat{indices} ); # vector spaces as <module> * (<e>)^<rep> 
    genes := GeneratorsOfAlgebra(ekge); # generators of ekge
    genes := List( genes, x -> MapstoLinearExtensionOfGroupHomomorphism( rep, x ) ); # list of matrix which degree is dim(<module>)
    genes := RepresentationMatrices( genes, vs, OnRight ); # generators of ekge as matrix
    module_e := GModuleByMats(genes,k); # a MTX-module <module> * (<e>)^<rep> on <ekge>

    # -- Create restriction of <module_e> to <h> --
    #  <h>  -> <ekge> ->  End_k{<module_e>},
    #   u  |->  u*e  |->    matrix
    genes := GeneratorsOfGroup( h ); 
    genes := List( genes, x -> MapstoLinearExtensionOfGroupHomomorphism( rep, x^emb * e ) ); # generators of ekge as matrix
    genes := RepresentationMatrices( genes, vs, OnRight );
    res := GModuleByMats(genes,k); # res of <module_e> , <ekge> to <kh>

    return rec(
        basis := emat{indices}, # a basis of <module_e> as submodule
        module := module_e, # a MTX-module <module> * (<e>)^<rep> on <ekge> 
        restriction := res  # res of <module_e> , <ekge> to <kh>
    );

end);


# This function calcurates representation.
# Remark : This function calucrates longer than <MatrixRepresentationByGModule>.
InstallGlobalFunction("MatrixRepresentationByModule", function(alg, m)
    local gens; # generators of <alg>

    gens := GeneratorsOfAlgebra(alg);
    # if Size(gnes) = 0 then ... ? 
    return AlgebraHomomorphismByImages(alg, MatrixAlgebra(m.field, m.dimension), gens, m.generators );
end);


# <alg> is an interior <g>-algebra record,
# <q> is a subgroup of <g>,
# <m> is a <alg.algebra>-module.
# This function returns the restricted module of <m> to <q>.
# If <m>.representation is bound, 
# then use <m>.representation.
InstallGlobalFunction("RestrictedModuleOfInteriorGAlgebra", function( alg, q, m )
    local a,st,rep,k, gens, res;

    if GeneratorsOfGroup(q) = [] then 
        q := Subgroup( q, [One(q)] );
    fi;

    a := alg.algebra;
    if IsBound( m.representation ) then 
        rep := m.representation;
    else 
        if not IsMutable( m ) then 
            m := MutableCopyGModule( m );
        fi;
        rep := MatrixRepresentationByModule(a, m);
        m.representation := rep;
    fi;

    gens := List( alg.generators , x -> x^rep );
    k := LeftActingDomain(a);
    res := GModuleByMats( gens, k );

    return res;
end);


# <a> is ( a record of interior <g>-algebra ) or ( a group <g> ),
# <h> is a subgroup of <g>,
# <m> is a module of ( <a.algebra> ) or ( <g> )
# This function returns the restricted module of <m> to <h>.
InstallGlobalFunction("RestrictedRightModule", function( a, h, m )
    local g;
    
    if IsRecord(a) then 
        return RestrictedModuleOfInteriorGAlgebra( a, h, m );
    elif IsGroup(a) then
        g := a;
        return RestrictedGModule( g, h, m );
    else 
        Error("<a> is not (a record of interior <g>-algebra or a group <g>).---------------------------------\n");
    fi;
    
end);


# <a> is ( a record of interior <g>-algebra ) or ( a group <g> ),
# <h> is a subgroup of <g>,
# <lMod> is a left module of ( <a.algebra> ) or ( <g> ),
# <t> is a function.
# This function returns the restricted left <h>-module of <lMod>.
#
# Remark:
#   関数の中で，<t> を通して一度 right module にしてから，restricted.
#   その後，<t>を通して再び left module に戻す．
InstallGlobalFunction("RestrictedLeftModule", function( a, h, lMod, t )
    local rMod, rRes;

    # args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        # # <args> = [ <a>, <h>, <lMod>(, <t>) ]
        # # If <t> is not given, then <t> is TransposedMat.
        # 
        # if not Size(args) in [4,3] then
        #     Error( "wrong number of arguments --------------------------\n");
        # fi;
        
        # args[1] := a;
        # args[2] := h;
        # args[3] := lMod;
        # if Size(args) = 4 then
        #     t := args[4];
        # elif Size(args) = 3 then
        #     t := TransposedMat;
        # fi;
    # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
    
    rMod := LeftModuleToRightModule( lMod, t );
    rRes := RestrictedRightModule( a, h, rMod );
    return RightModuleToLeftModule( rRes, t );

end);


# <a1> is (a record of an interior <g1>-algebra) or <g1>
# <h1> is a subgroup of <g1>,
# <a2> is (a record of an interior <g2>-algebra) or <g2>
# <h2> is a subgroup of <g2>.
# <m> is a <a1>-<a2>-bimodule,
# <t> is a function.
# This function returns the restricted <h1>-<h2>-bimodule of <m>.
# 
# # Remark:
#   関数の中で，<t> を通して一度 right module にしてから，restricted.
#   その後，<t>を通して再び left module に戻す．
InstallGlobalFunction("RestrictedBimodule", function( a1, h1, a2, h2, m , t )
    local tmp;
    
    tmp := RestrictedRightModule( a2, h2, m ); 
    tmp.lgenerators := RestrictedLeftModule( a1, h1, m, t ).lgenerators;

    return tmp;    
end);
