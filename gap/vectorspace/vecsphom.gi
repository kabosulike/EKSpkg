InstallGlobalFunction("DimensionOfImage", function( f )
    return RankMat(LinearMapRepMatrix(f).repmat);
end);

InstallGlobalFunction("IsZeroDimensionOfImage", function( f )
    local k;
    k := LeftActingDomain( Range(f) );
    return IsZeroMatrix( LinearMapRepMatrix(f).repmat , k) ;
end);


# <matfr> is a <n>x<n>-matrix ( <matfr> is a linear map on full rowspaces ),
# This function returns <mathom> in Hom_{<k>}(<S>, <V>),
# where <mathom> correspondence <matfr> : <S> -> <R>.
# <dimS> = dim(<S>), <dimR> = dim(<R>), <n> = <dimS>*<dimR>.
InstallGlobalFunction("MapstoCanonicalIsomorphismFullRowSpaceToHomSpace", function( matfr, dimS, dimR  )
    local n, mathom,x,vec;

    n := dimS*dimR;
    if Size(matfr) <> n then 
        Error("Size(matfr) <> dimS*dimR  ----------------------------  \n");
    fi;
    
    if dimS = 0 then 
        Error( "dimS = 0. -------------------------\n");
    fi;

    if dimR = 0 then 
        Error( "dimR = 0. -------------------------\n");
    fi;
    

    mathom := [];
    for x in [0..dimS-1] do
        vec := List( [1..dimR], i -> matfr[ i + x*dimR ] );
        Add( mathom, vec );
    od;

    return mathom;
end);


# <mathom> in Hom_{<k>}(<S>, <V>).
# This function returns a <n>x<n>-matrix <matfr>.
# Where <mathom> correspondence <matfr> : <S> -> <R>.
# <dimS> = dim(<S>), <dimR> = dim(<R>), <n> = <dimS>*<dimR>.
InstallGlobalFunction("MapstoCanonicalIsomorphismHomSpaceToFullRowSpace", function( mathom )
    local matfr;

    if Size(mathom) = 0 then 
        Error( "Size(mathom) = 0. -----------------------\n");
    fi;
    
    matfr := Concatenation( mathom );
    return matfr;
end);


#  M iso (direct sum of M_{i}) : an inner decomposition 
# <dims> : a list of dimension list of M_{i}.     i.e. dims[i] = dim(M_{i}).
# <ind> : an index of direct summand
# <k> : a finite field
InstallGlobalFunction("CanonicalProjectionByDirectSum", function( dims, ind , k )
    local nullMats, identityMat, proj, i;
    nullMats := List([1..Size(dims)], i -> NullMat( dims[i], dims[ind] , k ) ); # nullMats[i] correspondence zero map M_{i} -> M_{ind}
    identityMat := IdentityMat( dims[ind] , k); # Id : M_{ind} -> M_{ind}

    proj := []; # projection : M ->  M_{ind}
    for i in [1..Size(dims)] do # (number of direct summand ) times loop
        if i = ind then 
            Add(proj, identityMat);
        else 
            Add(proj, nullMats[i]);
        fi;
    od; # proj : List of matrices 

    proj := Concatenation(proj); # matrix

    return proj;
end);


InstallGlobalFunction("CanonicalInjectionByDirectSum",function( dims, ind, k )
    return TransposedMat( CanonicalProjectionByDirectSum( dims, ind, k) );
end);



# <matList> : a list of matrix with respect to indecomposition
# <ind> : an index of direct summand with respect to indecomposition
# <k> : a finite field
InstallGlobalFunction("InjectionByIndecompositionMats", function( matList , ind , k )
    local dimMod, dims, isoMat, inj;

    dimMod := Size(matList[1][1]); # dimension of parent module M
    dims := List( [1..Size(matList)], x->Size(matList[x]) ); # dimensions by indecomposition 
    isoMat := Concatenation(matList);                      #            (direct sum of M_{i}) -> M, isomorphism matrix.
    inj := CanonicalInjectionByDirectSum( dims, ind , k ); # M_{ind} -> (direct sum of M_{i})

    return inj * isoMat;                                   # M_{ind} -> (direct sum of M_{i}) -> M
end);


InstallGlobalFunction("ProjectionByIndecompositionMats", function( matList , ind , k )
    local dimMod, dims, isoMatInv, proj;

    dimMod := Size(matList[1][1]); # dimension of parent module M
    dims := List( [1..Size(matList)], x->Size(matList[x]) ); # dimensions by indecomposition 
    isoMatInv := Concatenation(matList)^-1;                     # M -> (direct sum of M_{i}) 
    proj := CanonicalProjectionByDirectSum( dims, ind , k );    #      (direct sum of M_{i}) -> M_{ind}
    
    return isoMatInv * proj;                                    # M -> (direct sum of M_{i}) -> M_{ind}
end);


InstallGlobalFunction("IdempotentByIndecompositionMatsInEndomorphismRing", function( matList, ind, k )
    local proj, inj, dims;
    dims := List( [1..Size(matList)], x->Size(matList[x]) );
    
    proj := ProjectionByIndecompositionMat( matList , ind , k ); # M -> (direct sum of M_{i}) -> M_{ind}
    inj := InjectionByIndecompositionMat( matList , ind, k);     # M_{ind} -> (direct sum of M_{i}) -> M 
    
    return proj * inj ; # an idempotent in end ring correspondence a direct summand M_{ind}
end);


InstallGlobalFunction("DecompositionProjection", function(decbasislist)
    local a,b,c,i,j,temp;
    # a:=[];
    # for i in [1..Length(decbasislist)] do#かっこ消したい
    #     Append(a,decbasislist[i]);
    # od;
    a:=Concatenation(decbasislist);
    b:=TransposedMat(Inverse(a));#ほんとはa^-1の列を取り出したいから転置して行取り出して戻す予定
    c:=[];
    temp:=1;
    for i in [1..Length(decbasislist)] do
        c[i]:=[];
        for j in [1..Length(decbasislist[i])] do#直和分解の因子の次元
            Add(c[i],b[temp]);
            temp:=temp+1;
        od;
    od;
    c:=List(c,TransposedMat);
    return c;#各直和因子に順番に対応するprojectionのリスト
end);


InstallGlobalFunction("InnerDecompositionProjection", function(decbasislist)
    local a,b,i;
    a:=DecompositionProjection(decbasislist);
    return List([1..Length(a)],i->a[i]*decbasislist[i]);
end);


# Left multiplication action
InstallGlobalFunction("OnLeft", function( pnt, elm )
    return elm * pnt;
end);


# This function returns a matrix of <elm>.
# <elm> acts on a vectorspace <vs> by action <act>.
InstallGlobalFunction("RepresentationMatrix", function( elm, vs, act )
    local bas, mat;

    bas := Basis( vs );
    mat := List( bas, pnt -> Coefficients( bas, act( pnt, elm ) ) );

    return mat;
end);


# This function returns a list of matrices.
InstallGlobalFunction("RepresentationMatrices", function( gens, vs, act )
    return List( gens, elm -> RepresentationMatrix( elm, vs, act ) );
end);


InstallGlobalFunction("IsEpimorphismMatrix", function( mat )
    return RankMat( mat ) = Size(mat[1]);
end);


InstallGlobalFunction("IsMonomorphismMatrix", function( mat )
    return RankMat( mat ) - Size( mat ) = 0;
end);


InstallGlobalFunction("LinearMapRepMatrixWithBasis", function(dombasis,codombasis,f)
    local mat,i;
    mat:=[];
    for i in [1..Length(dombasis)] do
        Add(mat,Coefficients(codombasis,dombasis[i]^f));
    od;
    return mat;
end);


InstallGlobalFunction("LinearMapRepMatrix", function(f)
    local db,cb,mat;
    db:=Basis(Source(f));
    cb:=Basis(Range(f));
    mat:= LinearMapRepMatrixWithBasis(db,cb,f);
    return rec(dombasi:=db,codombasis:=cb,repmat:=mat);
end);


InstallGlobalFunction("KernelOfLinearMapByMatrix", function( args... )
    local f, mat, k, basisS, basisR;

    # args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        if not Size(args) in [1,3] then
            Error( "Wrong Size(<args>)--------------------------\n");
        fi;
    
        if Size(args) = 2 then
            mat := args[1];
            k := args[2];
            basisS := Basis( FullRowSpace(k,Size(mat)) );
            basisR := Basis( FullRowSpace(k,Size(mat[1])) );
        elif Size(args) = 3 then
            basisS := args[1];
            mat := args[2];
            basisR := args[3];
        fi;
    
    # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 

    f := LeftModuleHomomorphismByMatrix( basisS, mat, basisR );
    return Kernel(f);
end);


#
# args
# <basisS> : a basis of full row space source f , where f is a linear map, 
# <basisR> : a basis of full row space range f, row vector list 
# <imgList> : a list of images of basisS by f  (i.e.  imgList[i] = f(basisS[i])  forall i )
# return 
# a representation matrix of f
InstallGlobalFunction("MatrixRepresentationOfLinearMapByImagesFullRowSpaces",function( basisS, basisR , imgList )
    local x,y;
    
    if Size(basisS) <> Size(imgList) then 
        Error("Size(basisS) <> Size(imgList) \n");
    fi;
    
    x := AsList(basisS);
    y := List( imgList , fv -> Coefficients( basisR, fv ) );
    return x^-1 * y; # representation matrix of f
end);


# args 
# <basisS> : [a basis of source ( unnecessary canonical and full row space )]
#                or source 
# <basisR> : [a basis of range ( unnecessary canonical and full row space )]
#                or range
# <imgList> : a list of images of basisS by f  (i.e.  imgList[i] = f(basisS[i])  forall i )
# return 
#   a representation matrix of f by <basisS> , <basisR>
InstallGlobalFunction("MatrixRepresentationOfLinearMapByImages", function( basisS, basisR, imgList , k )
    local frVecS, frVecR, frImgList, mat ;

    if IsVectorSpace(basisS) then 
        basisS := Basis(basisS);
    fi;
    if IsVectorSpace(basisR) then 
        basisR := Basis(basisR);
    fi;

    # replace full row space 
    frVecS := FullRowSpace( k, Size(basisS) );
    frVecR := FullRowSpace( k, Size(basisR) );
    frImgList := List( imgList, x -> Coefficients( basisR, x ) );
    mat := MatrixRepresentationOfLinearMapByImagesFullRowSpaces( Basis(frVecS), Basis(frVecR), frImgList );

    return mat;
end);