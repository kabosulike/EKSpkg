# <g> : group
# <k> < <h> < <g>: subgroups
# <rc> : right transversal of h/k
# <m> : g-module over f
InstallGlobalFunction("TraceMapOfEndmorphismRingWithRepresentative", function(g, h, k, rc, m)
    local mfh, mfk, r, u;

    if not IsSubgroup(g, h) then
        Error("error");
    fi;

    if not IsSubgroup(g, k) then
        Error("error");
    fi;

    if not IsSubgroup(h, k) then
        Error("error");
    fi;

    mfk := VectorSpace(m.field, MTX.BasisModuleEndomorphisms(RestrictedGModule(g,k,m)));
    mfh := VectorSpace(m.field, MTX.BasisModuleEndomorphisms(RestrictedGModule(g,h,m)));

    r := MatrixRepresentationByGModule(g, m);
    # return MappingByFunction(mfk, mfh, function(v)
    #     return Sum(List(rc, t -> Inverse(t)^r * v * t^r));
    # end
    # );
    return LeftModuleHomomorphismByImages(mfk, mfh, Basis(mfk), 
        List(Basis(mfk), v -> Sum(List(rc, t -> Inverse(t)^r * v * t^r))));
end);


# <g>: parent group
# <h>: subgroup of <g>
# <k>: subgroup of <h>
# <m>: mtx module of <g>
InstallGlobalFunction("TraceMap", function(g, h, k, m)
    return TraceMapOfEndmorphismRingWithRepresentative(g, h, k, RightTransversal(h, k), m);
end);


InstallGlobalFunction("TraceMapMatrix", function(g, h, k, m)
    local tr;
    tr:= TraceMap(g,h,k,m);
    return LinearMapRepMatrix(tr);
end);


# <g>: parent group
# <h>: subgroup of g
# <m>: module of g
InstallGlobalFunction("HigmansCriterion", function(g,h,m)
    local r,I,bh,bg,rc,tr;
	
    I := IdentityMat(m.dimension, m.field);
    bh := MTX.BasisModuleEndomorphisms(RestrictedGModule(g,h,m));
    bg:= MTX.BasisModuleEndomorphisms(m);
    rc := RightTransversal(g,h);

    tr:= TraceMapMatrix(g, g, h, m);

    return RankMat(tr.repmat) = Length(tr.codombasis);
end);
