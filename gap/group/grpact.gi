InstallGlobalFunction("IsActionFreelyWithAction", function(g,omega,act)
    local pnt, stab;
    for pnt in omega do 
        stab := Stabilizer(g,omega,pnt,act);
        if Size(stab) <> 1 then 
            return false;
        fi;
    od;
    return true;
end);


InstallGlobalFunction("IsActionFreely", function(args...)
    local g, omega,act;
    g := args[1];
    omega := args[2];
    if Size(args) = 2 then 
        act := OnPoints; # default action
    elif Size(args) = 3 then 
        act := args[3]; # user define action
    fi;    
    return IsActionFreelyWithAction(g,omega,act);
end);


# 群による置換行列を返す
InstallGlobalFunction("PermutationMatricesByGroupAction", function(G, S, F, Action)
    local mats, elms, d, zero, i, mat, j, o;
    elms := AsList( G );
    d    := Size(elms);
    zero := NullMat( d, d, F );
    mats := [];
    for i in [1..Size( S )] do
        mat := List( zero, ShallowCopy ); 
        for j in [1..d] do
            o := Position( elms, Action(elms[j], S[i]));
            mat[j][o] := One( F );
        od;
        mats[i] := mat;
    od;
    return mats;
end);


# <basis>: basis of kg
# <g>: group
# action: function(v, x)
# where <v>: element of kg
#       <x>: group element of g
#       the return value is the image of <v> under <x>
InstallGlobalFunction("GroupActionAsMatrices", function(basis, g, action)
    local mat, i;

    mat:= [];
    for i in [1..Length(basis)] do
        mat[i]:= Coefficients(basis, action(basis[i], g));
    od;

    return mat;
end);