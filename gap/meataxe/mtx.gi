InstallGlobalFunction("MutableCopyGModule", function( m )
    local copy;

    copy := ShallowCopy( m );
    if IsBound( copy.smashMeataxe ) and (not IsMutableBasis( copy.smashMeataxe ) ) then 
        copy.smashMeataxe := ShallowCopy( m.smashMeataxe );
    fi;
    
    return copy;
end);


InstallGlobalFunction("CheckMTXModule", function(module)

    if not IsBound( module.isMTXModule ) then 
        Error("not IsBound( module.isMTXModule )\n");
    fi;
    if not module.isMTXModule then 
        Error("not module.isMTXModule\n");
    fi;

    # return true;
    return;
end);


InstallGlobalFunction("IsMTXModule", function(m)
    if IsBound(m.isMTXModule) and m.isMTXModule then 
        return true;
    else
        return false;
    fi;
end);


InstallGlobalFunction("IsIsomorphicGModules", function(module1, module2)
    if not IsMutable(module1) then 
        module1 := MutableCopyGModule(module1);
    fi;

    if not IsMutable(module2) then 
        module2 := MutableCopyGModule(module2);    
    fi;
    
    return MTX.IsomorphismModules(module1,module2)<>fail;
end);
MTX.IsIsomorphic := IsIsomorphicGModules;
MTX.IsIsomorphicModules := IsIsomorphicGModules;
MTX.IsIsomorphicGModules := IsIsomorphicGModules;


# <g> : an integer or a (finite) group
# <k> : a finite field
# Retrun the zero module which has generators <gennum>.
InstallGlobalFunction("ZeroGModule", function(g, k)
    local zero, gennum;

    if IsGroup(g) then 
        gennum := Size(GeneratorsOfGroup(g));
    elif g in Integers then 
        gennum := g;
    else    
        Error( "Wrong type of <g> --------------------\n");
    fi;
    
    zero:= GModuleByMats([],0,k);
    zero.generators:= ListWithIdenticalEntries(gennum, EmptyMatrix(Characteristic(k)));
    zero.isZeroModule := true;
    zero.isProjective := true;
    zero.IsIrreducible := false;
    zero.IsAbsolutelyIrreducible := false;
    zero.isIndecomposable := false;
    return zero;
end);


# return 
#   trivial MTX-module . 
#   Admissible Size(GeneratorsOfGroup(g)) = 0.
InstallGlobalFunction("TrivialGModuleNonEmptyGenerators", function(g,k)
    local ngens;

    ngens := Size(GeneratorsOfGroup(g));
    if ngens = 0 then 
        ngens := 1;
    fi;
    
    return GModuleByMats(List([1..ngens],i->[[One(k)]]),1,k);    
end);


# <module> : MTX module
# return : 
#   is <module> trivial module (1-dim)
InstallGlobalFunction("IsTrivialGModule", function(module)
    local k;
    k := module.field;
    return module.dimension = 1 and ForAll( module.generators , x -> x[1][1] = One(k) );
end);


# args:
#   <m>, <n> : MTX modules
# return : Direct sum <m> and <n>
MTX_DirectSum@ := function( m, n )
    local genesMN, i , k ;

    if m.field <> n.field then 
        Error("<m> , <n> : different field. \n");
    fi;
    if Size(m.generators) <> Size(n.generators) then 
        Error("<m> , <n> : different size of generators. \n");
    fi;

    k := m.field;
    
    genesMN := []; # generators of direct sum <m> and <n> 
    for i in [1..Size(m.generators)] do 
        Add(genesMN, DiagonalMatrices( m.generators[i] , n.generators[i] , k ));
    od;

    return GModuleByMats( genesMN, k );
end;


# args : <list> is a list of MTX modules same length generators and same field.
# return : direct sum of modules in <list>.
MTX_DirectSumList@ := function( list )
    local directSum, i;

    if Size(list) = 0 then 
        return "Zero module";
    elif Size(list) = 1 then 
        return list[1];
    else
        directSum := list[1];
        for i in [2..Size(list)] do 
            directSum := MTX_DirectSum@( directSum , list[i] );
        od;
        return directSum;
    fi;
end;


MTX_DirectSumMultiplicity@ := function( m, mlty )
    return MTX_DirectSumList@( List([1..mlty], i -> m ) );   
end;


######  Summary of MTX_DirectSum  ######
# MTX.DirectSum( m1, m2 , ... ) : return direct sum of m1, m2, ... 
# MTX.DirectSum( list ) : return direct sum of MTX modules in <list>
# MTX.DirectSum( m, mlty ) : return direct sum of MTX modules <m> multiplicity <mlty>
# Remark : if length of <list> is 0 then return not MTX module.
# Remark : if length of <list> = [ m ] then return MTX module <m>.
MTX.DirectSum := function( args... )
    if Size(args) = 0 then 
        return MTX_DirectSumList@([]);
    elif Size(args) = 1 then 
        if not IsList( args[1] ) then # not list then args[1] is a MTX module
            args[1] := [args[1]]; # change form list
        fi;
        # else then <args> is a list of MTX modules

        return MTX_DirectSumList@( args[1] );

    elif Size(args) > 1 then 
        if args[2] in Integers then 
            return MTX_DirectSumMultiplicity@( args[1] , args[2] );
        else 
            # <args> is a list of MTX modules
            return MTX_DirectSumList@( args );
        fi;
    fi;
end;


# <module> is a MTX-module which has component <.generators> or <.lgenerators>.
# <t> is a function. 
#
# This function returns change right generators and left genaratros by <t>.
InstallGlobalFunction("ChangeRightLeftGenerators", function( module , t )
    local d, k, tmp, lgens, rgens, 
        dModule; # dual module of <module>
    
    d := module.dimension;
    k := module.field;
    tmp := [NullMat( d, d, k )];
    dModule := GModuleByMats( tmp, d, k ); # 一時的に, <tmp>で作成して，次の行で削除．
    Unbind( dModule.generators ); # GModuleByMats で作ると，<.generators>が出来てしまうので削除
        
    if IsBound( module.lgenerators ) then 
        rgens := List( module.lgenerators, t );
        dModule.generators := rgens;
    fi;

    if IsBound( module.generators ) then 
        lgens := List( module.generators , t );
        dModule.lgenerators := lgens;
    fi;
    return dModule;    
end);


# <module> is a MTX-module over <k>.
# <module> has component <.generators> or <.lgenerators>.
#
# This function returns the <k>-dual module <dModule> of <module>.
# The <k>-dual module determined by TransposedMat.
# Remark : 
#   If <module> has a component <.generators>, then the dual module <dModule> has <.lgenerators>.
#   If <module> has a component <.lgenerators>, then the dual module <dModule> has <.generators>.
InstallGlobalFunction("KDualOfModule", function( module )
    return ChangeRightLeftGenerators( module, TransposedMat );
end);
    

InstallGlobalFunction("TopOfGModule", function(m)
    if IsBound(m.top) then 
        return m.top;
    else
        return MTX.InducedActionFactorModule(m, MTX.BasisRadical(m));
    fi;
end);


InstallGlobalFunction("PrincipalIndecomposableModules", function(indecompoRegkG,irrs)
    local tops, q, pims,i,j;
    tops:=List(indecompoRegkG,x->TopOfGModule(x[2]));
    pims:=[];
    for i in [1..Length(irrs)] do
        for j in [1..Length(indecompoRegkG)] do
            if MTX.IsEquivalent(irrs[i],tops[j]) then
                q := indecompoRegkG[j][2];
                q.top := irrs[i];
                Add(pims, q);
                break;
            fi;
        od;
    od;
    return pims;
end);


# args
#   <g> : a finite group
#   <modoule> : a MTX-kg-module
# return 
#   true if <module> is faithful kg-module
#   false if otherwise
InstallGlobalFunction("IsFaithfulGModule", function(g,module)
    local rep;
    rep := MatrixRepresentationByGModule(g,module);
    return IsInjective(rep);
end);


InstallGlobalFunction("IsUniserialGModule", function(m)
    local a,i;
    a:=RadicalLayersOfGModule(m);
    for i in a do
        if not MTX.IsIrreducible(i) then
            return false;
        fi;
    od;
    return true;
end);


InstallGlobalFunction("FixedIrreduciblesCompositionFactorsMultiplicity", function(module, irrs)
    local cf,cf_tmp,t,i, copy;
    # if not IsMutable(module.smashMeataxe) then 
        copy := ShallowCopy(module);
        if IsBound(module.smashMeataxe) then 
            copy.smashMeataxe := ShallowCopy(module.smashMeataxe); # mutable
        fi;
    # fi;
    # cf_tmp := MTX.CollectedFactors(module);
    cf_tmp := MTX.CollectedFactors(copy); # record に .smashMeataxe が bind されているならば，.smashMeataxe の mutable が必要らしい
    cf:= ListWithIdenticalEntries(Length(irrs), 0);

    for t in [1..Size(cf_tmp)] do 
        for i in[1..Size(irrs)] do 
            if MTX.IsEquivalent(cf_tmp[t][1],irrs[i]) then 
                cf[i]:=cf_tmp[t][2];
                break;
            fi;
        od;
    od;
    return cf;
end);


InstallGlobalFunction("FixedIrreduciblesPIMsRadicalLayersMultiplicities", function(PIMs,irrs)
    local layer,i;
    layer:=[];
    for i in [1..Length(PIMs)] do
        Add(layer,FixedIrreduciblesRadicalLayerMultiplicities(PIMs[i],irrs));
    od;
    return layer;
end);


InstallGlobalFunction("EndmorphismAlgebraOfModule", function(m)
    return Subring(MatrixAlgebra(m.field,m.dimension),MTX.BasisModuleEndomorphisms(m));
end);


InstallGlobalFunction("IsBrick", function(m)
    if not MTX.IsIndecomposable(m) then
        return false;
    fi;
    if Length(m.smashMeataxe.basisEndoRad)<>0 then
        return false;
    fi;
    return IsDomain(EndmorphismAlgebraOfModule(m));
end);


InstallGlobalFunction("MTXMultiplicityModule", function(rho,d,k)
# args 
    # rho : G -> PGL(d,k)  ; a group hom
# return 
    # Multiplicity module determined by action rho.
    local p,q, g,gl , ker, pgl, pi, g_, pho_, t, geneM, projections;

    # notation
    p := Size(PrimeField(k));
    q := Size(k);
    g := Source(rho);
    gl := GL(d,k);
    ker := Subgroup( gl, [ Z(q)*IdentityMat(2,k) ]);
    pgl := FactorGroup( gl, ker );

    # homs 
    pi := NaturalHomomorphismByNormalSubgroup(gl, ker );

    # pull back
    g_ := Pullback(pi, rho); # gl, g の順
    projections := PullbackInfo(g_).projections; # gl, g
    pho_ := projections[1];

    # transversal 
    t := function(x)
        # arg : x in g
        # return : transversal of x 
        return Representative(PreImages( projections[2] , x )); 
    end;

    geneM := List( g , x -> (t(g))^pho_ );
    return rec( mltymodule := GModuleByMats( geneM, k ), pullback := g_);
end);



# args
    # <m1>, <m2> : MTX-modules
# return
    # Prepare --------------------------
    # <m1> and <m2> are weakly iso
    # :<=> 
    #       (i) ...  m1 and m2 are same dimension and 
    #       (ii)...  m1 and m2 have same length of generators and 
    #       (iii)... there exists permutation s in symmetric group n-letters
    #                   s.t. <m1Perm> and <m2> are iso as MTX-module.
    #
    #       Where, 
    #       n is the length of generators of <m1> , and 
    #       <m1Perm> is a MTX-module s.t. generated by [m1.generators acted by s].
    #       
    # Remark: 
    #   If <m1> and <m2> are iso as MTX-module
    #   then weakly iso.
    # --------------------------------------
    #  If not (i) and     (ii) , then return 1.
    #  If     (i) and not (ii) , then return 2.
    #  If not (i) and not (ii) , then return 3.
    #  If     (i) and     (ii) and <m1>,<m2> are     wealky iso , then return isomorphism matrix.
    #  If     (i) and     (ii) and <m1>,<m2> are not wealky iso , then return fail.
InstallGlobalFunction("WeaklyIsomorphismGModules", function( m1, m2 )
    local result, k, n, sym, perms, gensPerms, gens, m1Perm;

    # Error----
    if m1.field <> m2.field then 
        Error("modules field are different.\n-------------------------");
    fi;
    # ---------
    
    result := 0;
    if m1.dimension <> m2.dimension then  
        result := result + 1;
    fi;
    if Size(m1.generators) <> Size(m2.generators) then 
        result := result + 2;
    fi;
    if result <> 0 then 
        return result;
    fi;

    k := m1.field;
    n := Size(m1.generators);
    sym := SymmetricGroup(n);
    perms := Orbit(sym,[1..n], OnTuples);
    gensPerms := List( perms, x-> List( x , i -> m1.generators[i] ) );
    for gens in gensPerms do # permutation [generators of <m1>]
        m1Perm := GModuleByMats( gens, k ); 
        result := MTX.IsomorphismModules(m1Perm, m2);
        if result <> fail then 
            return result; # isomorphism 
        fi;
    od;
    return fail;
end);


InstallGlobalFunction("IsWeaklyIsomorphismGModules", function(m1,m2)
    local iso;
    iso := WeaklyIsomorphismGModules(m1,m2);
    if iso in Integers then 
        return iso = 0;
    else 
        return iso <> fail;    
    fi;
end);


# args
# <magmaElm> : element in magma
# <magmaRingElm> : element in magma ring
# <coeList> : coefficient list of <magmaRingElm>
# return 
# coefficient of <magmaElm> on <magmaRingElm>
InstallGlobalFunction("CoefficientInMagmaRingWithCoefficientsList", function( magmaElm , magmaRingElm , coeList )
    local pos;

    pos := Position( coeList, magmaElm );

    if pos <> fail then 
        return coeList[pos+1]; # coefficient
    else 
        return ZeroCoefficient(magmaRingElm);
    fi;
end);


InstallGlobalFunction("CoefficientInMagmaRing", function( magmaElm , magmaRingElm )
    local coeList, pos;
    coeList := CoefficientsAndMagmaElements(magmaRingElm);
    return CoefficientInMagmaRingWithCoefficientsList( magmaElm, magmaRingElm , coeList );
end);


# args 
# <idem> : an idempotent in a group algebra kg
# <module> : a MTX mod-kg
# <g> : a finite group 
# return 
#  dimension of <module>*<idem>
InstallGlobalFunction("DimensionOfDirectSummandOfGModuleWithRepresentation", function( idem, module , rep )
    local g, mat;
    g := Source(rep);
    mat := MapstoLinearExtensionOfGroupHomomorphism(rep, idem); # matrix of <idem> determined by <rep>
    return RankMat( mat );
end);


InstallGlobalFunction("DimensionOfDirectSummandOfGModule", function( idem, module , g )
    local rep;
    rep := MatrixRepresentationByGModule(g,module);
    return DimensionOfDirectSummandOfGModuleWithRepresentation( idem, module, rep );
end);


InstallGlobalFunction("DimensionOfImageRepresentationGModuleInEndRing", function( module, g )
    local rep, imgs, endRing, subSpace, k ;
    k := module.field;
    rep := MatrixRepresentationByGModule( g, module ); # representation  g -> GL
    imgs := List(AsList(g) , x->x^rep ); # matrix list
    
    endRing := MatrixAlgebra(k, module.dimension);
    subSpace := Subspace ( endRing, imgs );
    return Dimension(subSpace);
end);


# return 
#   MTX-module <module>^t 
InstallGlobalFunction("TwistedConjugationGModule", function(module , t , g )
    local rep, k , gens;
    k := module.field;
    rep := MatrixRepresentationByGModule( g, module ); # representation  g -> GL
    gens := List ( module.generators , x -> t^rep * x * (t^-1)^rep );
    return GModuleByMats( gens , k); # twisted 
end);


# args
#   <smallM> , <largeM> : modules
# return 
#   True if <smallM> is isomorphic to a direct summand of <largeM> , otherwise false.
MTX.IsDirectSummand:= function( largeM, smallM )
    local decSmall, decLarge, record;

    decLarge := IndecompositionGModuleList( largeM ); #  indecomposable summands of <largeM>
    decSmall := IndecompositionGModuleList( smallM ); #  indecomposable summands of <smallM>
    record := SubmultichooseFunction( decLarge , decSmall , MTX.IsomorphismModules );

    return record <> fail;    
end;

InstallGlobalFunction("IsDirectSummandOfModule", MTX.IsDirectSummand);