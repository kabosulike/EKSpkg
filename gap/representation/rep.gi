# make a GModule by a matrix representation
InstallGlobalFunction("GModuleByMatrixRepresentation", function(rep)
    local g, gl, matrices, n, f;
    g:= Source(rep);
    gl:= Range(rep);
    matrices:= List(GeneratorsOfGroup(g), x->x^rep);
    n:= DimensionOfMatrixGroup(gl);
    f:= DefaultFieldOfMatrixGroup(gl);
    return GModuleByMats(matrices, n, f);
end);


# make a matrix representation by a GModule 
# g の generators が empty list でもOK.
InstallGlobalFunction("MatrixRepresentationByGModule", function(g, m)
    local gens; # generators of <g>

    if Size(GeneratorsOfGroup(g)) = 0 then 
        gens := [One(g)];
    else
        gens := GeneratorsOfGroup(g);
    fi;

    return GroupHomomorphismByImages(g, GL(m.dimension, m.field), gens, m.generators);
end);


InstallGlobalFunction("RestrictedGModuleWithRepresentation", function(g, h, m)
    local r, gens;
    
    if Length(GeneratorsOfGroup(g)) = 0 then 
        g := Subgroup(g, [ One(g) ]);
    fi;
    r := MatrixRepresentationByGModule(g, m);
    gens:= GeneratorsOfGroup(h);
    if Length(gens) = 0 then
        gens:= [One(h)];
    fi;

    return rec( 
            module := GModuleByMats(List(gens, x->x^r), m.dimension,m.field),
            representation := r
    );

end);


InstallGlobalFunction("RestrictedGModule", function(g, h, m)
    return RestrictedGModuleWithRepresentation(g, h, m).module;    
end);


# <r> : rep of MTX-module <m>. Group hom <g> to GL(<m>).
InstallGlobalFunction("RestrictedGModuleGivenRepresentation", function(r, h, m)
    local gens, g;
    
    g := Source(r);
    if Length(GeneratorsOfGroup(g)) = 0 then 
        g := Subgroup(g, [ One(g) ]);
    fi;
    # r := MatrixRepresentationByGModule(g, m);
    gens:= GeneratorsOfGroup(h);
    if Length(gens) = 0 then
        gens:= [One(h)];
    fi;
    return GModuleByMats(List(gens, x->x^r), m.dimension,m.field);
end);


InstallGlobalFunction("RestrictedRepresentation", function(rep, h)
    local inclusion;
    inclusion := RestrictedMapping(IdentityMapping(Source(rep)), h);
    return inclusion*rep;
end);


InstallGlobalFunction("InductionOfGModule", function(g,h,m)

    if not IsSubgroup(g,h) then 
        Error( " Not subgroup <h> of <g> --------------------------\n.");
    fi;
    

    if Size(GeneratorsOfGroup(g)) = 0 then 
        g := Subgroup(g, [One(g)]);
    fi;
    if Size(GeneratorsOfGroup(h)) = 0 then 
        h := Subgroup(h, [One(h)]);
    fi;
    return InducedGModule(g,h,m);
end);


# on large enough finite field
# <g> : a finite group
# <p> : a prime number
InstallGlobalFunction("NumberOfIrreducibleModules", function( g, p )
    local ccList, ccpregList;
    ccList := ConjugacyClasses(g);
    ccpregList := Filtered( ccList , cc -> Order(Representative(cc)) mod p <> 0 );

    return rec(
        k := Size(ccList),   # the number of ordinary irr char of <g>
        l := Size(ccpregList)# the number of Brauer   irr char of <g>
    );
end);


# GModuleByMatrixRepresentation( phi^rep ); で代用できるので，
# この関数は不要．
RestrictedGModuleByHomomorphism@ := function( module, phi, rep )
    local k,gs,gr,gens;
    k := module.field;
    gs := Source(phi);
    # gr := Range(phi);
    # rep := MatrixRepresentationByGModule( g, module ); # representation : gr -> GL

    if Exist( List( GeneratorsOfGroup( gs ), x->x^phi ), y -> not y in Source(rep) ) then 
        Error("Exist( List( GeneratorsOfGroup( gs ), x->x^phi ), y -> not y in Source(rep) ) ----------\n");
    fi;
    
    gens := List( GeneratorsOfGroup( gs ), x->(x^phi)^rep  );# restriction rep : gs --phi--> g --rep--> GL  
    return GModuleByMats( gens , k ); # restriction  
end;


# args
#   args[1] : a k<g>-module <module>
#   args[2] : a group hom <phi>. デフォルトでは，<g> を Range(<phi>) とする．
#   args[3] : a group <g> or a representation <rep>.
#               Where, <rep> : <g> -> GL.
# return 
#   the restricted MTX-module of <module> by <phi>
InstallGlobalFunction("RestrictedGModuleByHomomorphism", function(args...)
    local module, g, phi, rep;

    module := args[1];
    phi := args[2];

    if Size(args) = 2 then 
        g := Range(phi);
        rep := MatrixRepresentationByGModule( g, module ); # representation : <g> -> GL

    elif Size(args) = 3 then 
        if IsGroup(args[3]) then 
            g := args[3];
            rep := MatrixRepresentationByGModule( g, module ); # representation : <g> -> GL
        elif IsMapping(args[3]) then
            rep := args[3]; # representation : <g> -> GL
        else 
            Error("args[3] is wrong type -----------------------\n");
        fi;

    else     
        Error("wrong number of arguments -------------------\n");
    fi;
    return RestrictedGModuleByHomomorphism@( module, phi, rep );
end);