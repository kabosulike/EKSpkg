# <e> is an idempotent in the fixed elements subalgebra <kg>^<h>,
# <h> is a subgroup of <g>,
# <a> is a subalgebra of a group algebra <kg>.
#
# This function returns the record of the localized interior <h>-algebra <eae>.
InstallGlobalFunction("IdempotentHeckeInteriorGAlgebra", function( e, h, a )
    local g, eae, st, emb, kg;

    kg := TopParent(a);
    g := UnderlyingMagma(kg);
    emb := Embedding(g,kg);
    eae := IdempotentHeckeAlgebraWithSmallGenerators( e, a );
    st := MappingByFunction( h, eae, x -> x^emb * e );
    # st := GroupHomomorphismByImages( h, eae, List( GeneratorsOfGroup(h), x-> x^Embedding(g,kg) * e ) );

    return rec(
        algebra := eae,
        structuralMap := st,
        one := e
    );
end);


InstallGlobalFunction("GroupRingAsInteriorGAlgebra", function( kg )
    local g;
    
    if not IsFreeMagmaRing(kg) then 
        Error(" <kg> is not a free magma ring. --------------------------------\n");
    fi;

    g := UnderlyingMagma(kg);

    return IdempotentHeckeInteriorGAlgebra( One(kg), g , kg );
end);


InstallGlobalFunction("LeftRegularModuleRowVector", function( G, F )
    local gens, mats, elms, d, zero, i, mat, j, o;

    gens := GeneratorsOfGroup(G);
    mats := List( gens, x -> false );
    elms := AsList( G );
    d    := Length(elms);
    zero := NullMat( d, d, F );
    for i in [1..Length( gens )] do
        mat := List( zero, ShallowCopy ); 
        for j in [1..d] do
            o := Position( elms, gens[i]*elms[j] );# if RightRegular , then gens[j]*elms[i].
            mat[j][o] := One( F );
        od;
        mats[i] := mat;
    od;
    return GModuleByMats( mats, F );
end);


InstallGlobalFunction("GroupAlgebraAsBimodule", function(g,k)
local d, rightReg, leftReg, gg, gens;

    d := Order(g);
    rightReg := RegularModule(g,k)[2];
    leftReg := LeftRegularModule(g,k);

    # (g.j,  1) -> Inverse(leftReg.generators[j]))
    # (1  ,g.i) -> rightReg.generators[i]
    gens := [];
    Append( gens ,List( leftReg.generators , Inverse ) );
    Append( gens , rightReg.generators );

    return GModuleByMats(gens, Order(g), k);# kg as right k[gxg]-module
end);


# <A>:subalgebra of a group ring kG
# return: <A>がgroup ring kGのsubalgebraなら，record (group:=G, field:=k, groupring:=kG, e:=embedding g->kG)を返す
# <A>がgroup ring kGのsubalgebraでないならエラーが出る
InstallGlobalFunction("ParentGroupRingInfo", function(A)
    local kg, g, e;
    kg:= TopParent(A);
    if not IsGroupRing(kg) then
        Error("A is not a subalgebra of a groupring.");
    fi;

    g:= UnderlyingMagma(kg);
    e:= Embedding(g, kg);

    return rec(group:= g, field:= LeftActingDomain(kg), groupring:= kg, embedding:= e);
end);



# b : a block of a gloup algebra kg
# d : a defect group of a block b
# k : large enough
InstallGlobalFunction("InertialGroup", function(b, d, kg)
local k, g, Br, kcgd, cgd, dcgd, ngd, blCgd, e, Emb, ngde;
    if not (b in kg) then 
        Error("not (b in kg) --------------------------\n" );
    fi;
    if not IsGroup(d) then # d = d0^g ( some defect group d0 )
        d := Representative(d);
    fi;

    k:= LeftActingDomain(kg);
    g:= UnderlyingMagma(kg);
    Br := BrauerMorphismOfGroupAlgebra(g,d,kg);
    kcgd := Range(Br); # kcgd is a subalgebra of kg
    cgd := Centralizer(g,d);
    dcgd := Subgroup(g, Concatenation(GeneratorsOfGroup(d),GeneratorsOfGroup(cgd)));
    ngd := Normalizer(g,d);

    # blCgd : blockidems of cgd associated with b
    # blCgd := BlockIdempotentsOfGroupAlgebra(cgd, kcgd);
    blCgd := PrimitiveDecompositionInSubgroupRing( One(kcgd), kcgd, cgd ).idempotents;
    blCgd := Filtered( blCgd , e-> e*(b)^Br <> Zero(kcgd) ); # error: b^Br が fail になる場合がある． b not in Source(Br) になっている．
    e := blCgd[1]; 

    Emb := Embedding( g , kg );
    ngde := SubgroupByProperty(ngd , n -> (n^Emb)^-1 * e * (n^Emb) = e );
    return ngde;
end);


InstallGlobalFunction("InertialQuotient", function(b, d, kg)
    local g, cgd, dcgd, ngde;
    g:= UnderlyingMagma(kg);
    cgd := Centralizer(g,d);
    dcgd := Subgroup(g, Concatenation(GeneratorsOfGroup(d),GeneratorsOfGroup(cgd)));
    ngde:= InertialGroup(b, d, kg);
    # return FactorGroup(ngde, dcgd);
    return rec(
        group := FactorGroup(ngde, dcgd),
        epimorphism := NaturalHomomorphismByNormalSubgroup(ngde, dcgd)
    );
end);


InstallGlobalFunction("InertialIndex", function(b,d,kg)
    return Order(InertialQuotient(b,d,kg).group);
end);


# <mcList> : list of form LinearCombinationCoefficientsAndMagmaElements.
#   i.e. mcList[2i] is a coefficient of mcList[2i-1], 
#           and mcList[2i-1] is a magma element
# <emb> : embedding : g -> rg, where rg is a magma ring.
# return 
#   element in rg correspondence of <mcList>  
InstallGlobalFunction("LinearCombinationCoefficientsAndMagmaElements", function(mcList, emb)
    local list;
    if Size(mcList) mod 2 <> 0 then 
        Error("Size(mcList) mod 2 <> 0 ---------------------------\n");
    fi;

    list := List( [1..QuoInt(Size(mcList),2)] , i-> (mcList[2*i-1])^emb * mcList[2*i] );
    return Sum(list);
end);



# Args 
#   <q> : a subgroup of <g>
#   <j> : an primitive idempotent in the <q>-fixed elements subalgebra <kg>^<q>
#   <kg> : the group algebra of <g> with coefficients in <k>
# Return
#   The normalizer N_{<g>}(<q>_{<delta>}) of a pointed group <q>_{<delta>}.
#   Where, <delta> is a point of <q> on <kg> such that <j> is contained in <delta>.
InstallGlobalFunction("NormalizerOfPointedGroupOnGroupAlgebra", function(q,j,kg)
    local norm, x, l, lkg, jkg, ngq, cgq, c, emb, g, qcgq;
    # Memo : 
    # qcgq が 遅いなら，cgq にする．qcgq, cgq で割るのは，計算を早くするためであって，結果は同じ．

    g := UnderlyingMagma(kg);
    emb := Embedding(g,kg);
    jkg := Subspace( kg, List(g, x->j*(x^emb)) );
    jkg := GBimoduleByRegularAction( q, g, jkg, kg ); # list
    jkg := jkg.gmodule; # record of MTX-module
    ngq := Normalizer(g,q);
    cgq := Centralizer(g,q);
    qcgq := Subgroup( g, Concatenation( GeneratorsOfGroup(q), GeneratorsOfGroup(cgq)) ); 

    # Calc the normalizer of a pointed group
    norm := []; # generators of normalizer N_{<g>}(<q>)
    c := qcgq; # ------  c = <cgq> or <qcgq>
    for x in RightCosets(ngq, c) do 
        x := Representative(x);
        l := j^(x^emb);
        lkg := Subspace( kg, List(g, x->l*(x^emb)) ); 
        lkg := GBimoduleByRegularAction( q, g, lkg, kg ); # list
        lkg := lkg.gmodule; # record of MTX-module

        if MTX.IsomorphismModules(lkg,jkg) <> fail then 
            Add( norm, x );
        fi;
    od; 
    norm := Subgroup(g, Concatenation(norm, GeneratorsOfGroup(c)) );

    return norm; # the normalizer N_{<g>}(<q>_{<delta>})
end);