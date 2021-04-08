# Definition ###################################
# A matrix <mat> is a binary relation matrix
#   :<=> mat[i][j] is integer for all i and j.
#
# mat[i][j] <> 0 のとき，関係をもつとみなし，
# mat[i][j] = 0  のとき，関係を持たないとみなす．
# ##############################################


# <mat> is a binary relation matrix.
# This function returns the reflexive closure matrix <newMat> of <mat>.
InstallGlobalFunction("ReflexiveClosure", function( mat )
    local newMat, i;
    
    newMat := ShallowCopy( mat );
    for i in [1..Size(mat)] do
        newMat[i][i] := 1;
    od;

    return newMat;
end);


# <mat> is a binary relation matrix.
# This function returns the symmetric closure matrix <newMat> of <mat>.
InstallGlobalFunction("SymmetricClosure", function( mat )
    local newMat, i, j;
    
    newMat := ShallowCopy( mat );
    for i in [1..Size(mat)] do
        for j in [1..Size(mat[1])] do
            if mat[i][j] <> 0 then
                newMat[j][i] := 1;
            fi;
        od;
    od;

    return newMat; 
end);


# <check> is a list. check[i] = true or false ( for all <i> ).
# この関数は<x>行目だけ計算する
# <x> からスタートしてたどり着ける場所が <tmp> に格納される．
#
# Assume that <mat>[i][j] >= 0 for all <i> and <j>.
InstallGlobalFunction("RecursionTransitiveClosure", function( tmp, mat, x, check )
    local connected, y;

    # Remark : 向きも考慮した connected 
    connected := Filtered( [1..Size(mat[x])], y -> mat[x][y] <> 0 ); # connected indices
    
    for y in connected do  
        tmp := tmp + mat[y];
        if not check[y] then 
            check[y] := true;
            tmp := RecursionTransitiveClosure( tmp, mat, y, check  );
        fi;
    od;

    return tmp;
end);


# <mat> is a binary relation matrix.
# This function returns the transitive closure matrix <newMat> of <mat>.
# Assume that <mat>[i][j] >= 0 for all <i> and <j>.
InstallGlobalFunction("TransitiveClosure", function( mat )
    local x0, check , i, j, newMat, tmp;
    
    newMat := ShallowCopy( mat );
    for x0 in [1..Size(mat)] do
        check := List( [1..Size(mat)], i -> false );
        tmp := mat[x0];
        tmp := RecursionTransitiveClosure( tmp, mat, x0, check );
        newMat[x0] := tmp;
    od;

    # 出力を整える
    for i in [1..Size(mat)] do
        for j in [1..Size(mat[1])] do
            if newMat[i][j] <> 0 then 
                newMat[i][j] := 1;
            fi;
        od;
    od;

    return newMat;
end);



# <mat> is a binary relation matrix.
# This function returns the equivalence closure matrix <newMat> of <mat>.
InstallGlobalFunction("EquivalenceClosure", function( mat )
    local newMat;

    newMat := ShallowCopy( mat );
    newMat := ReflexiveClosure( newMat );
    newMat := SymmetricClosure( newMat );
    newMat := TransitiveClosure( newMat );

    return newMat;
end);


# <mat> : a matrix
# This function show non-zero part of <mat>
InstallGlobalFunction("ShowNonZeroPart", function( mat )
    local i,j;
    for i in [1..Size(mat)] do
        for j in [1..Size(mat)] do
            if mat[i][j] <> 0 then 
                Print( "mat[",i,"]","[",j,"] = ", mat[i][j] , "\n");
            fi;
        od;
    od;
end);


# Arg : <mat> is a relation matrix
# Return : Simplify <newMat>. 
#   If mat[i][j] <> then newMat[i][j] = 1.
InstallGlobalFunction("SimplifyRelationMatrix", function( mat )
    local newMat, i, j;

    newMat := MutableCopyMat( mat );
    for i in [1..Size(mat)] do
        for j in [1..Size(mat[1])] do
            if mat[i][j] <> 0 then 
                newMat[i][j] := 1;
                # mat[i][j] := 1;
            fi;
        od;
    od;

    return newMat;    
end);
  
    


#
# Args
#   <mat> : a relation matrix satisfying <mat>[<i>][<j>] >= 0 for all <i> and <j>.
#   <list> : a list corresponding <mat>. Size(<list>) = Size(<mat>) = Size(<mat[1]>).
#   <eqRel> : an equivalence relation on [1..Size(list)]
# Return merge relation matrix of <mat> by <eqRel>.
# Remark : 関数の前後で，<mat>は不変．
#      ただし， <list> は変更される．
InstallGlobalFunction("MergeRelationMatrix", function( mat, list, eqRel )
    local i, j, newMat;

    # newMat := ShallowCopy(mat);
    newMat := MutableCopyMat(mat);

    # 途中で <newMat> の行と列のサイズが変わってしまうので，
    # for でなく while 
    i := 1;
    while i <= Size(newMat) do
        j := i + 1;
        while j <= Size(newMat[1]) do 
            if eqRel(i,j) then 
                # <newMat> の i 行目に j 行目を足す
                # <newMat> の i 列目に j 列目を足す
                # <newMat> の j 行目と j 列目を削除
                # <list>   の j 番目を削除

                # <newMat>
                    # - row
                    newMat[i] := newMat[i] + newMat[j];
                    Remove(newMat, j);
                    # - column
                    newMat := MutableCopyMat(TransposedMat(newMat));
                    newMat[i] := newMat[i] + newMat[j];
                    Remove(newMat, j);
                    newMat := MutableCopyMat(TransposedMat(newMat));

                # <list>
                    Remove(list, j);
                    continue; # Remove したら j は変更しない
            fi;
            j := j + 1;
        od;
        i := i + 1;
    od;

    return newMat;
end);

