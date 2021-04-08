InstallGlobalFunction("RadicalOfGModule", function(m)
    return MTX.InducedActionSubmodule(m,MTX.BasisRadical(m));
end);


InstallGlobalFunction("SocleOfGModule", function(m)
    return MTX.InducedActionSubmodule(m,MTX.BasisSocle(m));
end);


InstallGlobalFunction("HeartOfGModule", function(module)
    local vecM, radM, socM, m;

    m := MutableCopyGModule( module );
    # if IsMutable(module) or 
    #     (IsBound(module.smashMeataxe) and not IsMutable(module.smashMeataxe) ) then 
    #     m := ShallowCopy(module);
    # else 
    #     m := module;
    # fi;

    vecM := m.field^m.dimension;
    radM := Subspace( vecM, MTX.BasisRadical(m) );
    socM := Subspace( vecM, MTX.BasisSocle(m) );

    if IsSubspace( radM, socM ) then 
        radM := RadicalOfGModule(m);
        return MTX.InducedActionFactorModule( radM , MTX.BasisSocle(radM) );
    else
        return fail;
    fi;
    
end);


# radicalSeries contains non trivial radicals;
# Thus Length(radicalSeries) + 1 = the Loewy Length of <m>
# If <m> is semisimple then <radicalSeries> in return value is empty list.
# radicalSeries[i] = rad^i(m)
# This function add radicals and Loewy Length to <m>
InstallGlobalFunction("RadicalSeriesOfGModule", function(m)
    local a,b,radicals,basis,radicalLength;

    if not IsMutable(m) then 
        m := ShallowCopy(m);
    fi;

    radicals:= [];
    basis:= [];
    a:= MTX.BasisRadical(m);
    b:= m;
    while Size(a)<>0 do
        b:=MTX.InducedActionSubmodule(b,a);
        Add(radicals, b);
        Add(basis, a);
        a:=MTX.BasisRadical(b);
    od;
    radicalLength:= Length(radicals)+1;
    m.radicalSeries:= radicals;
    m.radicalLength:= radicalLength;
    return rec(radicalSeries:= radicals, basisList:= basis, radicalLength:= radicalLength);
end);


# Length(layers) = radical length of <m>
# layers[i] = rad^(i-1)(m)/rad^i(m)
InstallGlobalFunction("RadicalLayersOfGModule", function(m)
    local a,b,layers,i;
    a:=RadicalSeries(m);
    b:=m;
    layers:=[];
    for i in [1..Length(a.radicalSeries)] do
        Add(layers,MTX.InducedActionFactorModule(b,a.basisList[i]));
        b:=a.radicalSeries[i];
    od;
    Add(layers,b);
    return layers;
end);


InstallGlobalFunction("FixedIrreduciblesRadicalLayerMultiplicities", function(m,irrs)
    local a,b,i;
    a:=RadicalLayersOfGModule(m);
    b:=[];
    for i in [1..Length(a)] do
        Add(b,FixedIrreduciblesCompositionFactorsMultiplicity(a[i],irrs));
    od;
    return b;
end);


# Args 
#   args[1] = <module> : MTX-module
#   (args[2] = <irrs> : the set of all irreducible modules,  <.name> component は，あっても無くてもよい )
#   (or args[2] = <g> : a finite group )
# Return 
#   list of radycal layer name.
#   (irreducible modules name)
InstallGlobalFunction("RadicalLayersIrreduciblesName", function(args...)
# Remark: IrreducibleModules は，実行するたびに，irreducible modules の順番が変わることがあると思われる．
#         よって，<irrs> は固定した方がよいので，可能な限り <args> にいれた方がよい．
    local mat, length , list, r, c, tmp, mlty, x, k, module, irrs, g;

    module := args[1];
    k := module.field;
    if Size(args) = 2 then 
        if IsGroup(args[2]) then 
            g := args[2];
            irrs := IrreducibleGModules(g,k)[2]; 
        elif IsList(args[2]) and ForAll( args[2], MTX.IsIrreducible ) then
            irrs := args[2];
        else
            Error("args[2] is not (group or list of irreducible modules.)--------\n");
        fi;
    else 
        Error("Wrong Size(args) --------------\n");
    fi;

    if not IsBoundComponentName( irrs[1] ) then 
        AddIrreducibleNamesByDimension( irrs );
    fi;

    mat := FixedIrreduciblesRadicalLayerMultiplicities( module, irrs );
    length := Size(mat); # Loewy length

    list := []; # list of list ( do not matrix form in general )
    for r in [1..length] do   
        tmp := [];
        for c in [1..Size(irrs)] do # Size(irrs) = Size(mat[1])
            mlty := mat[r][c];
            if mlty <> 0 then 
                Add( tmp, [ irrs[c].name , mlty ] );
            fi;
        od;
        Add( list, tmp ); 
    od;

    # Show 
    # for x in list do
    #     Print(x,"\n");
    # od;
    # Print("\n");

    # return irrs;
    return list;
end);