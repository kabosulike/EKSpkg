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

#
	# <mo> is <q>-projective <g>-module
	# Return : a vertex group of <mo>
	# Description : This function checks subgroups of <q> sorted descending order.
	# Memo : <q> is not necessarily p-group
InstallGlobalFunction("VertexGroupOfGModuleDescending", function(g, q, mo)
	local ans, r;
	
	ans := q;
	for r in MaximalSubgroups(q) do
		if HigmansCriterion(g, r, mo) then 
			ans := VertexGroupOfGModuleDescending(g, r, mo);
			break;
		fi;
	od;

	return ans;
end);

#
	# <args> := [ g, mo, (ord, q) ]
	#	<q> is a subgroup of <g>,
	# 	<mo> is <q>-projective MTX <g>-module,
	# 	<ord> is an integer.
	# Default : 
	#	<ord> := 1,
	#	<q> := Sylow subgroup of <g>.
	# Memo : <q> is not necessarily p-group
	#
	# If ord =  1 then check subgroups of <q> ascending order.
	# If ord = -1 then check subgroups of <q> descending order. 
InstallGlobalFunction("VertexGroupOfGModule", function(args...)
	local g, mo, ord, p, q, r, sub, sz;

	# args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
		sz := Size(args);
		if sz in [2,3,4] then
			g := args[1];
			mo := args[2];
			ord := 1;

			p := Characteristic(mo.field);

			if sz >= 3 then 
				ord := args[3];			
			fi;

			if sz = 4 then 
				q := args[4];
			else 
				q := SylowSubgroup(g,p);
			fi;
		else
			Error( " ------------- wrong number of arguments --------------------------\n");
		fi;
	# args <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 
	

	if ord = 1 then 
		sub := ModularConjugacyClassesSubgroups(g, Characteristic(mo.field));
		sub := List(sub, Representative);
		sub := Filtered(sub, i->Order(i) <= Order(q));
		Sort(sub, function(q0, q1)
			return Order(Representative(q0)) < Order(Representative(q1));
		end);

		for r in sub do
			if HigmansCriterion(g, r, mo) then
			    return r;
			fi;
		od;

	elif ord = -1 then 
		return VertexGroupOfGModuleDescending(g, q, mo);
	fi;

	return fail;
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