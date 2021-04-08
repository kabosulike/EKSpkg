# <rMod> is a right module
# <t> is a function which sends matrix to matrix.
# This function returns the left module of <rMod> by <t>.
InstallGlobalFunction("RightModuleToLeftModule", function( rMod, t )
    local n,k,lgens, tmp;
    
    n := rMod.dimension;
    k := rMod.field;
    lgens := List( rMod.generators, t );
    tmp := GModuleByMats( [NullMat( n, n, k )], n, k );
    Unbind( tmp.generators );
    tmp.lgenerators := lgens;

    return tmp; # as left module of <rMod> by <t>
end);


# <lMod> is a left module,
# <t> is a function which sends matrix to matrix.
# This function returns the right module of <lMod> by <t>.
InstallGlobalFunction("LeftModuleToRightModule", function( lMod, t )
    local n,k,rgens;
    
    n := lMod.dimension;
    k := lMod.field;
    rgens := List( lMod.lgenerators, t );
    return GModuleByMats( rgens, n, k ); # as right module of <lMod> by <t>
end);
    

# <module> is a MTX-module,
# <lnum>, <rnum> are integers,
# <t> is a function.
# 
# This function returns a MTX-bimodule <bimod>.
# <bimod>.generators decompose to left generators and  right generators.
# left generators and right generators numbers are <lnum> and <rnum> respectively.
InstallGlobalFunction("RightModuleToBimodule", function( module, lnum, rnum, t )
    local n, rgens, lgens, bimod;

    if lnum + rnum <> Size( module.generators ) then 
        Error( "lnum + rnum <> Size( module.generators ). ---------------------\n" );
    fi;
    n := lnum + rnum;

    lgens := List( module.generators{[1..lnum]}, t );
    rgens := module.generators{[lnum+1..n]};

    bimod := GModuleByMats( rgens, module.dimension, module.field );
    bimod.lgenerators := lgens;
    return bimod;
end);
    

# <bimod> has a right generators <.generators> and a left generators <.lgenerators>.
# It returns a right module by a function <t>.
InstallGlobalFunction("BimoduleToRightModule", function( bimod , t )
    local gens, lgens, newgens;
    
    gens := bimod.generators;
    lgens := bimod.lgenerators;
    lgens := List( lgens, t );
    newgens := Concatenation( lgens, gens );

    return GModuleByMats( newgens, bimod.dimension, bimod.field );
end);


# <lMod1> and <lMod2> are left modules,
# <t> is a function matrix mapsto matrix.
InstallGlobalFunction("IsomorphismLeftModulesAsRightModules", function( lMod1, lMod2, t )
    local rMod1, rMod2;
    
    rMod1 := LeftModuleToRightModule( lMod1, t );
    rMod2 := LeftModuleToRightModule( lMod2, t );

    return MTX.IsomorphismModules( rMod1, rMod2 );
end);


InstallGlobalFunction("IsIsomorphicLeftModulesAsRightModules", function( lMod1, lMod2, t )
    return IsomorphismLeftModulesAsRightModules( lMod1, lMod2, t ) <> fail;        
end);
   

# <mod1> and <mod2> are bimodules.
#
# This function returns isomorphism <mod1_r> to <mod2_r>.
# Where, <mod1_r> and <mod2_r> are right module of <mod1> and <mod2> by <t> respectively.
InstallGlobalFunction("IsomorphismBimodulesAsRightModules", function( mod1, mod2, t )
    local mod1_r, mod2_r;
    
    mod1_r := BimoduleToRightModule( mod1, t ); # <mod1> as right module by <t>
    mod2_r := BimoduleToRightModule( mod2, t ); # <mod2> as right module by <t>

    return MTX.IsomorphismModules( mod1_r, mod2_r );
end);


InstallGlobalFunction("IsIsomorphicBimodulesAsRightModules", function( mod1, mod2, t )
    return IsomorphismBimodulesAsRightModules( mod1, mod2, t ) <> fail;
end);


# 群環<F><G>を<F>[<H>*<K>]加群としてみたときのGModuleを返す
InstallGlobalFunction("GroupRingAsBimodule", function(G, H, K, F)
    local lgens, rgens;
    lgens:=PermutationMatricesByGroupAction(G,GeneratorsOfGroup(H),F,function(g,h)
        return Inverse(h)*g;
        end);
    
    rgens:=PermutationMatricesByGroupAction(G,GeneratorsOfGroup(K),F,function(g,k)
        return g*k;
        end);
    
    return GModuleByMats(Concatenation(lgens,rgens),Order(G),F);
end);


# <kg>: group ring
# <h1>: subgroup of g
# <h2>: subgroup of g
# <w>: subspace of g on which <h1> and <h2> act from left and right respectively
# return: rec(basis, gmodule)
# where basis: basis of w,
#       gmodule: k[<h1>x<h2>]-gmodule of w w.r.t. the basis above
InstallGlobalFunction("GBimoduleByRegularAction", function(h1, h2, w, kg)
    local g, e, genL, genR, gens, B, x, hom;

    g:= UnderlyingMagma(kg);
    e:= Embedding(g, kg);

    genL:= List(GeneratorsOfGroup(h1), h-> h^e);
    genR:= List(GeneratorsOfGroup(h2), h-> h^e);

    gens:= [];
    B:= Basis(w);
    for x in genL do
        hom:= GroupActionAsMatrices(B, x, OnLeftInverse);
        Add(gens, hom);
    od;

    for x in genR do
        hom:= GroupActionAsMatrices(B, x, OnRight);
        Add(gens, hom);
    od;

    return rec(basis:= B, gmodule:= GModuleByMats(gens, Dimension(w), LeftActingDomain(w)));
end);