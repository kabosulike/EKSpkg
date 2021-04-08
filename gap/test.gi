InstallGlobalFunction(GModuleByMatrixRepresentation, function(rep)
    local g, gl, matrices, n, f;
    g:= Source(rep);
    gl:= Range(rep);
    matrices:= List(GeneratorsOfGroup(g), x->x^rep);
    n:= DimensionOfMatrixGroup(gl);
    f:= DefaultFieldOfMatrixGroup(gl);
    return GModuleByMats(matrices, n, f);
end);


InstallGlobalFunction(MatrixRepresentationByGModule, function(g, m)
    local gens; # generators of <g>

    if Size(GeneratorsOfGroup(g)) = 0 then 
        gens := [One(g)];
    else
        gens := GeneratorsOfGroup(g);
    fi;

    return GroupHomomorphismByImages(g, GL(m.dimension, m.field), gens, m.generators);
end);
