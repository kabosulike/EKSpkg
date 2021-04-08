InstallGlobalFunction("DisplayMatrixList", function(matList)
    local i;
    for i in [1..Size(matList)] do
        Display(matList[i]); 
        Print("\n");
    od;
end);


InstallGlobalFunction("PrintMatrixList", function(matList)
    local i;
    for i in [1..Size(matList)] do
        Print(matList[i]); 
        Print("\n");
    od;
end);


InstallGlobalFunction("DisplayMatrixListAndLine", function(matList)
    DisplayMatList(matList);
    Print("----------------------\n");
end);


InstallGlobalFunction("CanonicalMatrix", function( m, n , row, col , ring)
    local mat;
    if m = 0 or n = 0 then 
        return Error(" m = 0 or n = 0 --------------\n");
        # return NullMat(0,0,ring);
    fi;
    mat := NullMat(m,n,ring);
    mat[row][col] := One(ring);
    return mat;
end);


InstallGlobalFunction("LinearIndependentRows", function(mat)
    local mat2, indices;
    mat2 := TransposedMat(mat);
    indices := LinearIndependentColumns(mat2);
    return indices;    
end);


# <mat> : matrix
# <r1>,<c1>,<r2>,<c2> : natural numbers
# return 
#   a matrix <newMat> s.t. part of <mat> r1~r2 row, c1~c2 column.
InstallGlobalFunction("PartOfMatrix", function(mat, r1,c1, r2,c2)
    local newMat, r,c, tmp;

    newMat := [];
    for r in [r1..r2] do
        tmp := [];
        for c in [c1..c2] do
            Add(tmp, mat[r][c]);
        od;
        Add(newMat, tmp);
    od;
    return newMat;
end);


InstallGlobalFunction("NonZeroPosition", function(rowVec, ring) 
    local i;
    for i in [1..Size(rowVec)] do 
        if rowVec[i] <> Zero(ring) then 
            return i;
        fi;
    od;
    return fail;
end);


InstallGlobalFunction("IsZeroMatrix", function( mat, ring )
    local c, r, zeroMat ; 

    c := Size(mat[1]);# column
    r := Size(mat);#row
    zeroMat := NullMat(r,c, ring);

    return mat = zeroMat;
end);


# Args 
#   <args> := [ <mat> (, <ring> )]
# This function 
#   return true  if <mat> is a permutation matrix
#   return false otherwise.
InstallGlobalFunction("IsPermutationMatrix", function( args... )
    local list, v, i, possOne, possZero, mat , ring ;

    mat := args[1];
    if Size(args) = 1 then
        ring := Integers;
    elif Size(args) = 2  then
        ring := args[2];
    else
        Error( "Wrong Size(args)--------------------------\n");
    fi;


    if Size(mat) <> Size(mat[1]) then 
        return false;
    fi;

    list := List( [1..Size(mat[1])], i -> 0 );
    for v in mat do
        possOne := Positions( v, One(ring) );
        possZero := Positions( v, Zero(ring) );
        if (Size(possOne) <> 1) or (Size(possZero) <> Size(mat[1])-1 ) then 
            return false;
        fi;

        i := possOne[1];
        list[i] := list[i] + 1;
    od;

    return ForAll( list, i -> i = 1 );
end);