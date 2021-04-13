
InstallGlobalFunction("IsHomomorphismGModule", function(m1,mat_m1_to_m2,m2)
    local mat,actm1,actm2,i;
    mat:=mat_m1_to_m2;
    actm1:=m1.generators;
    actm2:=m2.generators;
    for i in [1..Length(actm1)] do
        if actm1[i]*mat<>mat*actm2[i] then
            return false;
        fi;
    od;
    return true;
end);


# <m> and <s> are MTX <a>-modules,
# 
# This function returns a basis of Hom_{<a>}(<m>,<s>).
# This function uses transposed matrices.
InstallGlobalFunction("BasisModuleHomomorphismsByTransposedMat", function( m, s )
    local ts, tm, thom, hom;
    
    ts := ShallowCopy( s );
    tm := ShallowCopy( m );
    
    ts.generators := List( s.generators, TransposedMat );
    tm.generators := List( m.generators, TransposedMat );
    thom := MTX.BasisModuleHomomorphisms( ts, tm );

    hom := List( thom, TransposedMat ); # basis of Hom_{<a>}(<m>,<s>)

    return hom;
end);
    

# Let <mod1> and <mod> be MTX <a>-modules.
# This function returns a basis of homspace Hom_{<a>}( <mod1>, <mod2> ).
# We can use this function even if <mod2> is irreducible.
InstallGlobalFunction("BasisModuleHomomorphisms", function( mod1, mod2 )

    if not IsMutable( mod2 ) then 
        mod2 := MutableCopyGModule( mod2 );
    fi;
    
    
    if MTX.IsIrreducible(mod2) then # <mod2> is mutable
        return BasisModuleHomomorphismsByTransposedMat( mod1, mod2 );
    else 
        return MTX.BasisModuleHomomorphisms( mod1, mod2 );
    fi;
end);

# <m>: a GModule
# return: the maximum subspace of <m> acted trivialy by G
InstallGlobalFunction("BasisInvariantsOfGModule",function(m)
    local d,equ,i,j,idm;
    d:=m.dimension;
    idm:=IdentityMat(d);
    equ:=HorizontalJointedMats(List(m.generators,x->x-idm));
    return NullspaceMat(equ);
end);

InstallGlobalFunction("TransTensorToMat",function(dimU,dimV,one_one_tensor)
    local i,j,M;
    M:=[];
    for i in [1..dimU] do
        M[i]:=[];
        for j in [1..dimV] do
            M[i][j]:=one_one_tensor[(i-1)*dimV+j];
        od;
    od;
    return M;
end);
InstallGlobalFunction("HorizontalJointedMats",function(mats)
    local tmats;
    tmats:=List(mats,x->TransposedMat(x));
    return TransposedMat(Concatenation(tmats));
end);

# <a>,<b>: natural numbers
# <abvec>: a vector whose length equals to <a><b>
# return: the (<a>,<b>)-matrix which is splited into by <abvec>  
InstallGlobalFunction("SpritVactorIntoMatrix",function(a,b,abvec)
    local i,j,M;
    M:=[];
    for i in [1..a] do
        M[i]:=[];
        for j in [1..b] do
            M[i][j]:=abvec[(i-1)*b+j];
        od;
    od;
    return M;
end);

# Hom(U,W)~(U* \otimes W)^G
# <m1>,<m2>: GModules
# return: the basis corresponding the camoninal basis of U* \otimes W by the above natural above isomorphims
InstallGlobalFunction("AlternativeBasisModuleHomomorphisms",function(m1,m2)
    local dualm1,dualm1tensorm2,inv;
    dualm1:=DualGModule(m1);
    dualm1tensorm2:=TensorProductGModule(dualm1,m2);
    inv:=BasisInvariantsOfGModule(dualm1tensorm2);
    return List(inv,x->ImmutableMatrix(m1.field,TransTensorToMat(m1.dimension,m2.dimension,x)));
end);

# Arg
#   <record> is a record with RecNames 
#       [ x", "y", "z", "f", "r" ]. 
#
# Where <x>, <y>, <z> are modules and <f>, <r> are hom matrices
# <f> : <x> -> <y>,
# <r> : <z> -> <y>.
#
# This function returns a hom matrix <s> : <x> -> <z>
#   such that <f> = <s>*<r>.
# If there is not such <s>,
#   this function returns fail.
#   
# Remark :
#   Unnecessary <f> is the identity.
InstallGlobalFunction("SectionOfHomomorphismMatrix", function( record )
    local 
        r,f,x,y,z,k,
        xz, xy,
        mats, 
        matsCoe, fCoe, sCoe, s;
    
    # args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        r := record.r; # matrix <z> -> <y>
        x := record.x; # module 
        y := record.y; # module
        z := record.z; # module
        k := x.field;
        if IsBound(record.f) then 
            f := record.f; # matrix <x> -> <y>
        elif x = y then
            f := IdentityMat( x.dimension, k );
        fi;

        # Check
        CheckSameFields( x, y, z );
        CheckSizeLinearmapMatrix( x, f, y );
        CheckSizeLinearmapMatrix( z, r, y );
    # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 
        

    # Given a retraction <r>,
    # calc a section <s> : <x> -> <z>
        xz := BasisModuleHomomorphisms( x, z );
        xy := BasisModuleHomomorphisms( x, y );
        mats := List( xz, s_ -> s_*r ); # elements in Hom(<x>,<y>)

        matsCoe := List( mats, m -> Coefficients( Basis(VectorSpace(k,xy)), m ) );
        fCoe := Coefficients( Basis(VectorSpace( k, xy )), f ); 

        sCoe := SolutionMat( matsCoe, fCoe );
        if sCoe = fail then 
            return fail;
        else 
            s := LinearCombination( xz, sCoe );
            return s;
        fi;
end);


# <m1> and <m2> are modules,
# <mat> is a homomorphism matrix <m1> to <m2>.
#
# This function returns a matrix <s>.
# Where <s> is a section of <mat>.
# If there is not a section of <mat>,
# this function returns fail.
InstallGlobalFunction("SectionOfSplitEpimorphismMatrix", function( m1, mat, m2 )
    local record, s;

    if not IsEpimorphismMatrix( mat ) then 
        return fail;
    fi;

    record := rec( 
        x := m2,
        y := m2,
        z := m1,
        r := mat, # <z> -> <y>
    );
    s := SectionOfHomomorphismMatrix( record ); # matrix or fail

    return s;
end);


InstallGlobalFunction("IsSplitEpimorphismMatrix", function( m1, mat, m2 )
    return SectionOfSplitEpimorphismMatrix( m1, mat, m2 ) <> fail;
end);



# Arg
#   <record> is a record with RecNames 
#       [ x", "y", "z", "f", "s" ]. 
#
# Where <x>, <y>, <z> are modules and 
# <f>, <s> are matrices
# <f> : <x> -> <y>,
# <s> : <x> -> <z>.
# 
# This function returns a matrix <r> : <z> -> <y>
#   such that <f> = <s>*<r>.
# If there is not such <r>,
#   this function returns fail.
#
# Remark :
#   Unnecessary <f> is the identity.
InstallGlobalFunction("RetractionOfHomomorphismMatrix", function( record )
    local s,f,x,y,z,k, rec2;
    
    # args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        s := record.s; # matrix <x> -> <z>
        f := record.f; # matrix <x> -> <y>
        x := record.x; # module 
        y := record.y; # module
        z := record.z; # module
        k := x.field;
        if IsBound(record.f) then 
            f := record.f; # matrix <x> -> <y>
        elif x = y then
            f := IdentityMat( x.dimension, k );
        fi;
        CheckSameFields( x, y, z );
    # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 

    x.generators := List( x.generators, TransposedMat );
    y.generators := List( y.generators, TransposedMat );
    z.generators := List( z.generators, TransposedMat );

    rec2 := rec( 
        x := y, # change <x>, <y>
        y := x, 
        z := z, 
        r := TransposedMat(s),
        f := TransposedMat(f),
    );

    return TransposedMat( SectionOfHomomorphismMatrix(rec2) );

end);


# <m1   > and <m2> are modules,
# <mat> is a homomorphism matrix <m1> to <m2>.
#
# This function returns a retraction matrix of <mat>.
# If there is not a retraction of <mat>,
# then this function returns fail.
InstallGlobalFunction("RetractionOfSplitMonomorphismMatrix", function( m1, mat, m2 )
    local m1_, m2_, s_; 

    m1_ := ShallowCopy(m1);
    m2_ := ShallowCopy(m2);

    m1_.generators := List( m1_.generators, TransposedMat );
    m2_.generators := List( m2_.generators, TransposedMat );
    
    s_ := SectionOfSplitEpimorphismMatrix( m2_, TransposedMat( mat ), m1_ );
    if s_ <> fail then 
        return TransposedMat( s_ );
    else 
        return fail;
    fi;
end);


# <m1> and <m2> are modules,
# <mat> is a homomorphism matrix <m1> to <m2>.
#
# This function returns 
#   true if <mat> is a split monomorphism,
#   false otherwise.
InstallGlobalFunction("IsSplitMonomorphismMatrix", function( m1, mat, m2 )
    return RetractionOfSplitMonomorphismMatrix( m1, mat, m2 ) <> fail;
end);


# <record> is a record with RecNames
#   [ "y", "z", "beta", "v" ].
#
# <y>, <z> and <v> are modules over <k>,
# <beta> is a hom mat <y> to <z>.
#
# If <bv> is split epi, then this function returns a section of <bv>.
# Otherwise this function returns fail.
# Where <bv> := <beta> \otimes_<k> <id_v>.
InstallGlobalFunction("SectionOfTensorSplitEpimorphism", function( record )
    local y, z, b, v, id, yv, zv, bv, k;
    
    # args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        y := record.y;
        z := record.z;
        b := record.beta;
        v := record.v;

        CheckSameFields( y, z, v );
        k := y.field;
    # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 
    
    id := IdentityMat( v.dimension, k );# identity of <v> 

    yv := TensorProductGModule( y, v );
    zv := TensorProductGModule( z, v );
    bv := KroneckerProduct( b, id );

    return SectionOfSplitEpimorphismMatrix( yv, bv, zv );
end);


InstallGlobalFunction("IsTensorSplitEpimorphism", function( record )
    return SectionOfTensorSplitEpimorphism( record ) <> fail;
end);
    


# Remark : 合ってるか心配なのでコメントアウト
#	epi が存在する ならば rank = mod2.dimension は正しそうだが，
#	逆が正しいか不明．
# 
# # @
#     # <mod1> and <mod2> are <a>-modules.
#     # This function 
#     #   returns true if there exists <a>-epimorphism <mod1> to <mod2>,
#     #   return false otherwise.
# ExistEpimorphismModules := function( mod1, mod2 )
#     local bas, mat, rank;

#     bas := BasisModuleHomomorphisms( mod1, mod2 );
#     if bas = [] then 
#         rank := 0;
#     else
#         mat := ConcatenationMatrixListVertical( bas );
#         rank := RankMat(mat);
#     fi;
    
#     return rank = mod2.dimension;
# end;


# args
# <rho> : group hom
# <magmaRingElm> in magma ring
# return 
#  rho(magmaRingElm) : image of <magmaRingElm> by linear extension of <rho> 
InstallGlobalFunction("MapstoLinearExtensionOfGroupHomomorphism", function(rho, magmaRingElm )
    local g;
    g:= Source(rho);
    return Sum( List( AsList(g) , x -> CoefficientInMagmaRing( x, magmaRingElm ) * x^rho ) ); 
end);


# <x> and <y> are modules,
# <mat> is a homomorphism matrixx <x> to <y>
InstallGlobalFunction("CheckSizeLinearmapMatrix", function( x, mat, y )
    if Size(mat) <> x.dimension then 
        Error( "--------------- Size(mat) <> x.dimension ----------------------------\n" );
    elif Size(mat[1]) <> y.dimension then 
        Error( "--------------- Size(mat[1]) <> y.dimension ----------------------------\n" );
    fi;
end);