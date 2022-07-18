# args := [ <g>, <h>, <m> ] or [<h>, <m>]
# Where <h> is a subgroup of <g>.
#   Case (i) : args = [ <g>, <h>, <m> ]
#       <m> is a <g>-module
#   Case (ii) : args = [<h>, <m>]
#       <m> is a <h>-module
# return 
#   Case (i) : Brauer morphism of End_{k}( Res(<g>,<h>,<m>) )
#   Case (ii): Brauer morphism of End_{k}( <m> )
InstallGlobalFunction("BrauerMorphismOfEndRing", function(args...)
    local mfh, n, cc, k, tr, mfk, g, h , m ;


    if Size(args) = 3 then
        g := args[1];
        h := args[2];
        m := args[3];
    elif Size(args) = 2 then
        h := args[1];
        m := args[2];
        g := h;
    else
        Error( "wrong number of arguments --------------------------\n");
    fi;
    

    if not IsSubgroup(g, h) then
        Error("not IsSubgroup(g, h) -------------------\n");
    fi;

    mfh := VectorSpace(m.field, MTX.BasisModuleEndomorphisms(RestrictedGModule(g,h,m)));

    n := TrivialSubspace(mfh);
    for cc in ConjugacyClassesSubgroups(h) do
        if h in cc then
            continue;
        fi;
        for k in cc do
            tr := TraceMap(g, h, k, m);
            mfk := VectorSpace(m.field, MTX.BasisModuleEndomorphisms(RestrictedGModule(g,k,m)));
            n := n + Subspace(mfh, List(Basis(mfk), b -> b^tr));
        od;
    od;
    return NaturalHomomorphismBySubspace(mfh, n);
end);


InstallGlobalFunction("VertexClassOfGModule", function(g, m)
    local
    cc,
    c;
    

    if IsBound(m.vertexClass) then 
        return m.vertexClass;
    fi;

    if Size(GeneratorsOfGroup(g)) = 0 then 
        return g^g;
    fi;

    # if not MTX.IsIndecomposable(m) then
    #     Error("This module is not indecomposable.");
    # fi;

    cc := ModularConjugacyClassesSubgroups(g, Characteristic(m.field));

    Sort(cc, function(c1, c2)
        return Order(Representative(c1)) < Order(Representative(c2));
    end);

    for c in cc do
        if HigmansCriterion(g, Representative(c), m) then
            return c;
        fi;
    od;

	return fail;
end);


InstallGlobalFunction("VertexGroupOfGModule", function(g, m)
    # if IsBound then it use.
    if IsBound(m.vertexGroup) then 
        return m.vertexGroup;
    elif IsBound(m.vertexClass) then 
        return Representative(m.vertexClass);
    fi;

    # if not IsBound then calc vertex class.
    return Representative(VertexClassOfGModule(g,m));
end);


InstallGlobalFunction("VertexClassOfGModuleAddRecord", function(g,m)
    if not IsMutable(m) then 
        m := ShallowCopy(m);
    fi;
    m.vertexClass := VertexClassOfGModule(g,m);

    if Order(Representative(m.vertexClass)) = 1 then 
        m.isProjective := true;
    else 
        m.isProjective := false;
    fi;
    return m;
end);


InstallGlobalFunction("VertexGroupOfGModuleAddRecord", function(g,m)
    if not IsMutable(m) then 
        m := ShallowCopy(m);
    fi;
    m.vertexGroup := VertexGroupOfGModule(g,m);
    if Order(m.vertexGroup) = 1 then 
        m.isProjective := true;
    else 
        m.isProjective := false;
    fi;
    return m;
end);


InstallGlobalFunction("SourceModuleOfGModuleAddRecord", function(g,m)
    local q, src;

    if not IsMutable(m) then 
        m := ShallowCopy(m);
    fi;
    if IsBound(m.vertexGroup) then 
        q := m.vertexGroup;
    elif IsBound(m.vertexClass) then 
        q := Representative(m.vertexClass);
    else
        m.vertexClass := VertexClassOfGModule(g,m);
        q := Representative(m.vertexClass);
    fi;

    src := SourceOfGModule(g,m,q);
    m.sourceModule := src;

    return m;
end);


InstallGlobalFunction("VertexGroupSourceModuleOfGModuleAddRecord", function(g,m)
    VertexGroupOfGModuleAddRecord( g, m );
    SourceModuleOfGModuleAddRecord( g, m );
    return m;
end);


InstallGlobalFunction("HomogeneousComponentsOfGModuleAddVertexClass", function(g,m)
    local hc;
    hc := MTX.HomogeneousComponents(m);
    ForEach( hc, x -> VertexClassOfGModuleAddRecord( g, x.component[2] ) );
    return hc;
end);


InstallGlobalFunction("HomogeneousComponentsOfGModuleAddVertexClassSourceModule", function(g,m)
    local hc;
    hc := MTX.HomogeneousComponents(m);
    ForEach( hc, x -> VertexClassOfGModuleAddRecord( g, x.component[2] ) );
    ForEach( hc, x -> SourceModuleOfGModuleAddRecord( g, x.component[2] ) );
    return hc;
end);


InstallGlobalFunction("HomogeneousComponentsOfGModuleAddVetexGroupSourceModule", function(g,m)
    local hc;
    hc := MTX.HomogeneousComponents(m);
    ForEach( hc, x -> VertexGroupOfGModuleAddRecord( g, x.component[2] ) );
    ForEach( hc, x -> SourceModuleOfGModuleAddRecord( g, x.component[2] ) );
    return hc;
end);


InstallGlobalFunction("SourceOfGModule", function(g, m, v)
    local
    I, # indecomposable summands of m restricted to v
    t,
    II, # indecomposable summands of
    tt;

    # if not MTX.IsIndecomposable(m) then
    #     Error("This module is not indecomposable.");
    # fi;

    if Size(GeneratorsOfGroup(v)) = 0 then
        v := Subgroup(g, [One(g)]); # Generatorが空リストにならない単位群を作るため
    fi;
    
    I := List(MTX.HomogeneousComponents(RestrictedGModule(g, v, m)), h->h.component[2]);
    for t in I do
        II := List(MTX.HomogeneousComponents(InductionOfGModule(g, v, t)), h->h.component[2]);
        
        for tt in II do
            if MTX.IsomorphismModules(m, tt) <> fail then
                return t;
            fi;
        od;
    od;
end);