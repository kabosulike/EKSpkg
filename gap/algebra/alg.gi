InstallGlobalFunction("TopOfAlgebra", function(alg)
    local rad;
    rad := RadicalOfAlgebra(alg);
    return alg/rad;
end);


# Reference : 62.4 
# Example ^^^^^^^^^^^^^^^^^^^^
# tensor of algebras use structure constant 
InstallGlobalFunction("TmpCoefficient", function( v_ij, v_kl, v_mn , table1, table2 )
# v_ij = [i,j] , i : index of basis of algebra1, j : index of basis of algebra2
# table1 : structure constant of algebra1 
# return structure constant of (tensor algebra1 and angebra2 )
    local i,j,k,l,m,n, pos1,pos2, coe1, coe2;

    # indices of bases
    i := v_ij[1]; j := v_ij[2];
    k := v_kl[1]; l := v_kl[2];
    m := v_mn[1]; n := v_mn[2];

    # 
    pos1 := Position(table1[i][k][1], m); # table1[i][k][1] : list of indexes satisfying coe is non zero.
    pos2 := Position(table2[j][l][1], n); 
    if pos1 = fail or pos2 = fail then 
        # table には non zero に対応する index (と coe)しか入っていないから，
        # その中でヒットしないということは，index m に対応する term の coe は 0 ということ．
        return 0;
    else 
        coe1 := table1[i][k][2][pos1]; # coefficient
        coe2 := table2[j][l][2][pos2]; # coefficient
        return coe1 * coe2;
    fi;

    return fail;
end);


TmpBijection@ := function( ij, dim2 ) # bijection ijList to [1..dim1*dim2]
# ijList is a list [[1,1],[1,2],...,[dim1,dim2]],
# dim2 is a dimention of algebra2.
    local i,j;
    i := ij[1]; j := ij[2];
    return i*dim2 + j;
end;


InstallGlobalFunction("TmpBijection", function( ij, dim2 )
# dim2 is a dimention of algebra2
    return TmpBijection@( ij - [1,1] , dim2 ) + 1;# -[1,1], +1 : index の調整
end);


InstallGlobalFunction("TensorAlgebrasByStructureConstants", function( algebra1, algebra2 )
    local table1, table2, dim1, dim2, ijSet, t, 
    e_ij, e_kl, x_ij, y_kl, list, e_mn, a,
    fld;

    CheckSameFields( algebra1, algebra2 );
    fld := LeftActingDomain( algebra1 );
    
    table1 := StructureConstantsTable(Basis(algebra1));
    table2 := StructureConstantsTable(Basis(algebra2));
    dim1 := Dimension(algebra1);
    dim2 := Dimension(algebra2);
    ijSet := Concatenation(List ( [1..dim1] , i->List( [1..dim2] , j ->[i,j] ) ));
    t := EmptySCTable(dim1*dim2, Zero(fld));
    for e_ij in ijSet do 
        for e_kl in ijSet do 
            x_ij := TmpBijection(e_ij,dim2); # correspondence e_ij
            y_kl := TmpBijection(e_kl,dim2);
            
            list := [];
            for e_mn in ijSet do
                # unnecessary remove zero element
                list := Concatenation(list, [TmpCoefficient(e_ij, e_kl, e_mn, table1, table2) , TmpBijection(e_mn, dim2) ] );# Add coefficient, index. 
            od ;
            SetEntrySCTable( t, x_ij, y_kl, list );
        od;
    od;
    a := AlgebraByStructureConstants(fld,t); # tensor algebra of algebra1 and algebra2

    return a;
end);


InstallGlobalFunction("OppositeStructureConstantsTable", function( alg )
    local opTbl, i, j , tbl, n, k ;
    
    n := Dimension( alg );
    tbl := StructureConstantsTable( Basis(alg) );
    k := LeftActingDomain( alg );

    # if tbl[n+1] = 1 then # symmetric
    #     return tbl;
    # fi;

    opTbl := EmptySCTable( n, Zero(k) );
    for i in [1..n] do
        for j in [1..n] do
            opTbl[i][j] := tbl[j][i];
        od;
    od;

    return opTbl;
end);


InstallGlobalFunction("EnvelopingAlgebraByStructureConstants", function( alg )
    local k, opTbl, opAlg;
    opTbl := OppositeStructureConstantsTable( alg );
    k := LeftActingDomain( alg );
    opAlg := AlgebraByStructureConstants( k, opTbl );

    return  TensorAlgebrasByStructureConstants( opAlg, alg );
end);