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
    for k in MaximalSubgroups(h) do
		tr := TraceMap(g, h, k, m);
		mfk := VectorSpace(m.field, MTX.BasisModuleEndomorphisms(RestrictedGModule(g,k,m)));
		n := n + Subspace(mfh, List(Basis(mfk), b -> b^tr));
    od;
    return NaturalHomomorphismBySubspace(mfh, n);
end);


# <mo> is a MTX <g>-module,
# <q> is a subgroup of <g>
# Return true iff <q> is a precisely vertex of a <g>-module <mo>
InstallGlobalFunction("IsPreciselyVertex", function(g, q, mo)
	local r;
	if not HigmansCriterion(g, q, mo) then return false; fi ;

	for r in MaximalSubgroups(q) do 
		if HigmansCriterion(g, r, mo) then 
			return false;
		fi;
	od;
	return true;
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
	local ans, r, que, qi, cu;

	que := []; # queue
	qi := 0; # index of que
	ans := q; # answer

	Add(que, q);
	qi := qi + 1;

	while qi <= Size(que) do 
		cu := que[qi]; # current 
		qi := qi + 1;
		ans := cu;

		for r in MaximalSubgroups(cu) do # g-conj で類別しても良い
			if HigmansCriterion(g, r, mo) then 
				Add(que, r);
			fi;
		od;

	od;
	
	if IsMutable(mo) then mo.vertex := ans; fi;
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
				if IsMutable(mo) then mo.vertex := r; fi;
				return r;
			fi;
		od;

	elif ord = -1 then 
		r := VertexGroupOfGModuleDescending(g, q, mo);
		if IsMutable(mo) then mo.vertex := r; fi;
		return r;
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



# <mo> is a MTX <g>-module with vertex <vx>
#	i.e. <mo> is a precisely <vx>-projective
# memo : <mo> is not necessarily indecomposable
# Return : a source module of <mo>
InstallGlobalFunction("SourceOfGModule", function(g, mo, vx)
	local res, hc, i, s;
	
	res := RestrictedGModule(g, vx, mo);
	hc := MTX.HomogeneousComponents(res);

	for i in hc do
		s := i.component[2];
		if IsPreciselyVertex(vx, vx, s) then 
			if IsMutable(mo) then mo.source := s; fi;
			return s;
		fi;
	od;
	
	return fail;

end);