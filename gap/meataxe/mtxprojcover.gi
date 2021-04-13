InstallGlobalFunction("MinimalSubGModules", function(irr, m) 
    local  homs, e, mats, i;
    if MTX.IsIrreducible(irr)<>true then
        Error("Argument <irr> is not an irreducible module");
    fi;
    homs:=SMTX.Homomorphisms(irr, m);
    if homs=[] then
        return [];
    fi;
    SMTX.SortHomGModule(irr, m, homs);

    e:=SMTX.DegreeFieldExt(irr);
    if e > 1 then
        homs:=homs{Filtered([1..Length(homs)],i->(i mod e) = 1)};
    fi;
    mats:=List(homs,i->ImmutableMatrix(irr.field,i));
    return mats;
end);


# Topにあってirrと同型なものそれぞれに対して対応するMaximalを返す
# こちらも可変引数にしたいが、、
InstallGlobalFunction("MaximalSubGModules", function(irr,m)
    local d,u,dirr;
        dirr:=SMTX.DualModule(irr);
        if MTX.IsIrreducible(dirr)<>true then
        Error("Argument <irr> is not an irreducible module");
        fi;
    d:=SMTX.DualModule(m);
    u:=MinimalSubGModules(dirr,d);
    return List(u,i->SMTX.DualizedBasis(d,i));
end);


InstallGlobalFunction("ExtendToBasis", function(subbasis,supdim,field)
    local subdim,zero,one,sub,leadpos;
    zero:=Zero(field);
    one:=One(field);
    subdim:=Length(subbasis);
    if subdim=0 then
        return IdentityMat(supdim)*one;
    fi;
        subbasis:=TriangulizedMat(subbasis);
        leadpos:=SubGModLeadPos(subbasis,supdim,subdim,zero);
        sub:=ShallowCopy(subbasis);
        Append(sub,(IdentityMat(supdim)*one){Difference([1..supdim],leadpos)});
        sub:=ImmutableMatrix(field,sub);
    return sub;
end);


InstallGlobalFunction("SubSpaceQuotientMatrix", function(subbasis,supdim,field)
    local extbasis,modulo,subdim;
        extbasis:=ExtendToBasis(subbasis,supdim,field);
        subdim:=Length(subbasis);
        modulo:=NullMat(subdim,supdim-subdim,field);
        Append(modulo,IdentityMat(supdim-subdim,field));
        modulo:=extbasis^-1*modulo;
    return ImmutableMatrix(field,modulo);
end);


# <args> = [ <module>, <PIMs>(, <irrs> )]
InstallGlobalFunction("ProjectiveCoverOfGModule", function( args... )
    local module, PIMs, irrs, 
        i,j,k,maximals,homs,componentsmat,components,quot,supdim,field;
    # if module="Zero GModule" then
    #     return rec(Epimorphism:=[],ProjectiveCover:="Zero GModule",BasisOfSyzygy:=[]);
    # fi;

    # args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        if not Size(args) in [2,3] then
            Error( "Wrong Size(<args>)--------------------------\n");
        fi;
    
        module := args[1];
        if Size(args) = 3 then
            PIMs := args[2];
            irrs := args[3];
        elif Size(args) = 2 then
            PIMs := args[2];
            irrs := List( PIMs, q -> TopOfGModule( q ) );
        fi;
    # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 

    field:=module.field;

    if IsBound( module.isZeroModule ) and module.isZeroModule then 
        return rec( 
            epimorphism := [], 
            module := ZeroModule( Size(module.generators), field ),
            # projectiveCover := MTX.DirectSum(components),
            basisOfSyzygy := []
        );
    fi;

    supdim:=module.dimension;
    maximals:=List(irrs,x->MaximalSubGModules(x,module));
    componentsmat:=[];
    components:=[];
    for i in [1..Length(irrs)] do
        homs:=BasisModuleHomomorphisms(PIMs[i],module);
        for j in [1..Length(maximals[i])] do
            quot:=SubSpaceQuotientMatrix(maximals[i][j],supdim,field);
            k:=1;
            while homs[k]*quot=Zero(homs[k]*quot) do
                k:=k+1;
            od;
            Add(componentsmat,homs[k]);
            Add(components,PIMs[i]);
            Remove(homs,k);
        od;
    od;
    componentsmat:=Concatenation(componentsmat);
    return rec( 
        epimorphism :=componentsmat, 
        module := MTX.DirectSum(components),
        # projectiveCover := MTX.DirectSum(components),
        basisOfSyzygy := NullspaceMat(componentsmat)
    );
end);


InstallGlobalFunction("IsProjectiveGModule", function(module,PIMs,irrs)
    local pc;

    if IsBound( module.isProjective ) then 
        return module.isProjective;
    fi;

    if IsBound( module.isZeroModule ) and module.isZeroModule then 
        return true;
    fi;

    if IsBound( module.vertexGroup ) then 
        return Order( module.vertexGroup ) = 1;
    fi;

    pc := ProjectiveCoverOfGModule( module, PIMs, irrs );  
    return pc.basisOfSyzygy = [];
end);

   