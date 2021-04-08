InstallGlobalFunction("SortMatrixRowVectorByNonZeroPosition", function(m, ring)
    local mCopy;
    mCopy := ShallowCopy(m);
    Sort( mCopy , 
        function(rowVec1, rowVec2) 
            local pos1, pos2;
            pos1 := NonZeroPosition(rowVec1,ring);
            pos2 := NonZeroPosition(rowVec2,ring);
            if pos1 = fail then pos1 := Size(m[1])+1; fi;
            if pos2 = fail then pos2 := Size(m[1])+1; fi;
            # return NonZeroPosition(rowVec1,ring) < NonZeroPosition(rowVec2,ring);
            return pos1 < pos2;
        end 
    );
    return mCopy;
end);


InstallGlobalFunction("NonZeroPositionToOne", function(matrix, field)    
    local i , rowVec, a , mat;
    
    mat := ShallowCopy(matrix);
    for i in [1..Size(mat)] do 
        rowVec := mat[i];
        if NonZeroPosition(rowVec, field) <> fail then 
            a := rowVec[NonZeroPosition(rowVec, field)];
            mat[i] := rowVec*Inverse(a);
        fi;
    od;
    return mat;
end);


InstallGlobalFunction("RowStairsMatrix", function( matrix, field ) # 階段行列
# mat is a matrix which entry belong to a field.
    local mat, row, i, pos, a;

    mat := ShallowCopy(matrix);
    for row in [1..Size(mat)] do 
        mat := SortMatrixRowVectorByNonZeroPosition(mat,field);# ver 1-0-0 , mat := Sort... に変更
        mat := NonZeroPositionToOne(mat, field);
        # Display(mat);
        
        pos := NonZeroPosition( mat[row] , field);
        if pos <> fail then 
            for i in [row+1..Size(mat)] do 
                a := mat[i][pos];
                if a <> Zero(field) then 
                    mat[i] := mat[i] - (mat[row] * a);
                fi;
            od;
        fi;

    od;
    return mat;
end);


InstallGlobalFunction("RowCanonicalForm", function( mat , field ) 
    local mat2, r, r2, pos, a,b, list;
    mat2 := RowStairsMatrix(mat, field);
    list := [1..Size(mat2)];
    Sort( list, function(x,y) return x >= y; end );
    for r in list do # row
        pos := NonZeroPosition( mat2[r], field );
        if pos <> fail then 
            for r2 in [1..(r-1)] do # row
                a := mat2[r][pos];
                b := mat2[r2][pos];
                mat2[r2] := mat2[r2] - (b*(a^-1))*mat2[r];
            od;
        fi;
    od;
    return mat2;
end);


InstallGlobalFunction("DirectsumComplement", function(mat, k)
# mat is a matrix which size n x m  (n < m).
# mat is correspondence matrix of inner direct product of w in v.
# Where, v is a vector space on a field k with dimension m , and 
#        w is a subspace of v with dimension n .
# This function return a matrix complementMat size (m-n) x m .
# complementMat correspondence inner direct product of y in v,
#   where  v = w + y and y is a orghogonal complement space of w.
    local stairsMat, nonZeroPosList, n, m, j, i, complementMat;

    stairsMat := RowStairsMatrix(mat, k);
    nonZeroPosList := List( stairsMat, rowVec -> NonZeroPosition(rowVec, k) );
    # if Exist(nonZeroPosList , fail) then
    #     Error(" Error in a function [ DirectsumComplement ] -------------------.\n" );
    #     Error(" mat is not correspondence a subspace .\n" );
    # fi;

    n := Size( mat ); # dimension w. w is a subspace of v .
    m := Size( mat[1] );    # dimension v     
    complementMat := NullMat( m-n , m , k); 

    j := 1;
    for i in [1..Size(complementMat)] do # Size(complementMat) = dim y .
        while  j in nonZeroPosList do 
            j := j+1;
        od;
        complementMat[i][j] := One(k);
        j := j+1;
    od;

    return complementMat;
end);


# args
#   <mat1>,<mat2> : matrices on <ring>
#   <ring> : a ring
# return 
#    <largeMat> is a matrix which form 
# [
#    mat1 , zero,
#    zero, mat2
## ]
DiagonalMatrices@ := function(mat1, mat2, ring)
    local mat1Row, mat1Col, mat2Row, mat2Col,largeMatRow, largeMatCol, r, c, largeMat;

    # We want mat1, mat2 are matrices (i.e. list of list ).
    if not IsList(mat1[1]) then # row Size = 1
        for c in [1..Size(mat1)] do # col 
            mat1[c] := [mat1[c]];
        od;
    fi;
    if not IsList(mat2[1]) then # row Size = 1
        for c in [1..Size(mat2)] do # col 
            mat2[c] := [mat2[c]];
        od;
    fi;

    # Prepare
    mat1Col := Size(mat1[1]);  # col size of mat1
    mat1Row := Size(mat1);     # row size of mat1
    mat2Col := Size(mat2[1]);
    mat2Row := Size(mat2);
    largeMatRow := mat1Row + mat2Row;
    largeMatCol := mat1Col + mat2Col;

    # Create a big matrix <largeMat>
    largeMat := NullMat(largeMatRow, largeMatCol, ring);
    for r in [1..largeMatRow] do 
        for c in [1..largeMatCol] do
            if r <= mat1Row and c<= mat1Col then # upper left
                largeMat[r][c] := mat1[r][c] * One(ring);
            elif r > mat1Row and c> mat1Col then # bottom right
                largeMat[r][c] := mat2[r-mat1Row][c-mat1Col] * One(ring);
            fi;
        od;
    od;

    return largeMat;
end;


InstallGlobalFunction("DiagonalMatrices", function( args... )
    if Size(args) = 2 then 
        # Default args[3] is Rationals.
        return DiagonalMatrices@( args[1], args[2] , Rationals );
    elif Size(args) = 3 then 
        return DiagonalMatrices@( args[1], args[2], args[3] );
    fi;
end);


InstallGlobalFunction("DiagonalMatrixList", function( matList, ring )
    local tmp, i ;

    if Size(matList) = 0 then 
        return [];
    elif   Size(matList) = 1 then 
        return matList[1];
    fi;

    tmp := matList[1];
    for i in [2..Size(matList)] do 
        tmp := DiagonalMatrices( tmp , matList[i]  , ring );
    od;

    return tmp;
end);


InstallGlobalFunction("AdjustMatrixListForm", function( matrixList )
    local matList2, i ;

    matList2 := [];
    for i in [1..Size(matrixList)] do 
        if (not IsMatrix( matrixList[i] ) ) and ( IsList(matrixList[i]) ) then 
            Add( matList2 , [matrixList[i]]); # adjust vector to matrix
        else 
            Add( matList2, matrixList[i]);
        fi;
    od;
    return matList2;
end);


# <mat1>, <mat2> are matrix s.t. Size(mat1) = Size(mat2) (i.e. same row lenght)
# return concatenation matrix <mat1> and <mat2>
InstallGlobalFunction("ConcatenationMatrix", function( mat1, mat2 )
    local mat, r;

    if Size(mat1) <> Size(mat2) then 
        Error("Different length of mat1 and mat2. \n");
    fi;

    mat := [];
    for r in [1..Size(mat1)] do # row 
        Add ( mat , Concatenation(mat1[r], mat2[r]) ) ; # add row vec
    od;
    return mat;
end);


# <matList> : a list of matix
InstallGlobalFunction("ConcatenationMatrixListVertical", function(matList)
    matList := AdjustMatrixListForm(matList);
    return Concatenation(matList);
end);


InstallGlobalFunction("ConcatenationMatrixListHorizontal", function(matList)
    local transMatList, transBigMat;

    matList := AdjustMatrixListForm(matList);
    transMatList := List( matList, x -> TransposedMat(x) ); # transposed matrix list
    transBigMat := ConcatenationMatrixListVertical( transMatList );
    return TransposedMat( transBigMat );
end);


# Remark: args order <largeMat>, <smallMat>
InstallGlobalFunction("EmbeddingMatrixToMatrix", function( largeMat , smallMat, x, y )
    local copySmallMat, copyBigMat, r, c;

    copySmallMat := ShallowCopy(smallMat);
    copyBigMat := ShallowCopy(largeMat);

    if Size(smallMat) = 0 then 
        return largeMat;
    fi;

    if not IsList(copySmallMat[1]) then 
        for r in [1..Size(copySmallMat)] do 
            copySmallMat[r] := [copySmallMat[r]];
        od;
    fi;


    for r in [1..Size(copySmallMat)] do # row
        for c in [1..Size(copySmallMat[1])] do  # column
            copyBigMat[r+(x-1)][c+(y-1)] := copySmallMat[r][c];
        od;
    od;

    return copyBigMat;
end);


# decomposition <mat> to list of matrix 
InstallGlobalFunction("MatrixDecompositionRowBlock", function(mat, rowSizeList)
    
    local newMat, ind, tmp, i;

    if Sum(rowSizeList) <> Size(mat) then 
        Error("Sum(rowSizeList) <> Size(mat) -------------\n");
    fi;

    newMat := [];
    ind := 1;
    for i in [1..Size(rowSizeList)] do 
        tmp := [];
        for i in [1..rowSizeList[i]] do 
            Add( tmp , mat[ind] );
            ind := ind+1;
        od;
        Add( newMat, tmp );
    od;

    return newMat;
end);


# args
#   <lam> : an eigen value
#   <d>   : a natural number
#   <k>   : a finite field containing <lam>
# return 
#   Jordan block of <lam> with degree <d> 
InstallGlobalFunction("JordanBlock", function(lam, d , k )
    local mat1, mat2;
    
    mat1 := IdentityMat(d,k) * lam ;
    mat2 := EmbeddingMatrixToMatrix( IdentityMat(d-1,k), NullMat(d,d,k) , 1, 2 );
    
    return mat1 + mat2;
end);


# args order different ver
InstallGlobalFunction("JordanCell", function(d, lam , k)
    return JordanBlock(lam,d,k);    
end);


# Args :
#   <mat> : a matrix 
#   <x1>, <y1>, <xLen>, <yLen> : integers 
# Return :
#   A sub matrix <mat2> of <mat1>.
#   Where 
#       <mat2> is <xLen>x<yLen>-matrix
#       
#       <mat2> は，<mat> の (<x1>,<y1>)-成分から
#       <xLen>,<yLen> だけ取り出した matrix.
InstallGlobalFunction("PickUpMatrixBlock", function( mat, x1, y1, xLen, yLen )
    local mat2, i, j;

    mat2 := List( [1..xLen] , 
                i -> List( [1..yLen], j -> 0 )  
            );
    for i in [1..xLen] do
        for j in [1..yLen] do
            mat2[i][j] := mat[ x1 + i - 1 ][ y1 + j -1 ];
        od;
    od;
    return mat2;
end);