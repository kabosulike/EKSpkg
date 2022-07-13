InstallGlobalFunction("BlockIdempotentsOfGroupAlgebra", function(kg)
    return BlockDecomposition(kg).idempotents;
end);


InstallGlobalFunction("DefectClassOfBlockOfGroupAlgebra", function(b,kg)
# b : a block of a group algebra kg 
# b in kg が前提
    local cc, I, i, q, br, p ,k, g , syl, cg, coes;

    if not b in kg then 
        Error("not b in kg -----------------------\n");
    fi;

    g := UnderlyingMagma(kg);
    k := LeftActingDomain(kg);
    p := Size(PrimeField(k));
    syl := SylowSubgroup(g,p);
    cg := Centralizer(g,syl);
    coes := CoefficientsAndMagmaElements(b);
    # # DihedralGroup で ，Intersection(AsList(cg), coes) がエラー．
    #       Example: g:= D(24), p=2, k = GF(2^2). 
    #               Then AsList(cg)[1] = <identity> of ...
    # if Size(Intersection(AsList(cg), coes)) <> 0 then 
    #     # b の C_{<g>}(<syl>) 部分の係数で，0 でないものが存在するならば，
    #     # b の defect group は Sylow p-subgroup.
    #     return syl^g;
    # fi;
    
    cc := ConjugacyClassesSubgroups(g);
    cc := Filtered(cc, x -> 
            FixedPrimeRegularSingularPartInt(p , Order(Representative(x))).p_prime_part = 1
          );
    I := [1..Size(cc)];
    Sort(I, function(i,j)
        return Order(Representative(cc[i])) > Order(Representative(cc[j]));
    end);
    for i in I do
        q := Representative(cc[i]); 
        br := BrauerMorphismOfGroupAlgebra(g,q,kg); 
        if b^br <> Zero(kg) then
            return q^g; 
        fi;
    od;

    return fail;
end);


InstallGlobalFunction("DefectGroupOfBlockOfGroupAlgebra", function(b,kg)
    return  Representative( DefectClassOfBlockOfGroupAlgebra(b,kg) );
end);
# ? long time
# DefectClassOfBlockOfGroupAlgebraAndStructureDescription := function(b,kg)
#     local dcs;
#     dcs := DefectClassOfBlockOfGroupAlgebra(b,kg); # defect group classes
#     Error();
#     return rec(
#         defectClasses := dcs,
#         structures := List(dcs, x->StructureDescription(Representative(x)))
#     );
# end;


# args
# <c> : block idem of a group algebra kh
# <h> : subgroup of <g>
# <emb>: embedding <h> -> <kg>
# <kg> : group algebra
# return 
#   true iff c is the principal block of <kh>
InstallGlobalFunction("IsPrincipalBlockIdempotentWithSubgroupAndEmbedding", function( c, h, emb, kg )
    local g , sumh;    

    if not c in kg then 
        Error(" not <c> in <kg> -----------------------\n");
    fi;

    g := UnderlyingMagma(kg);
    sumh := Sum( List( h , x -> x^emb ) );

    return c * sumh <> Zero(kg);
end);


InstallGlobalFunction("IsPrincipalBlockIdempotent", function( b, kg )
    local g , emb, sumg;    

    g := UnderlyingMagma(kg);
    emb := Embedding(g,kg);
    return IsPrincipalBlockIdempotentWithSubgroupAndEmbedding( b, g, emb, kg );
end);
# IsPrincipalBlockIdempotent := function( b, kg )
#     local g , emb, sumg;    
#     g := UnderlyingMagma(kg);
#     emb := Embedding(g,kg);
#     sumg := Sum( List( g , x -> x^emb ) );
#     return b * sumg <> Zero(kg);
# end;


InstallGlobalFunction("PrincipalBlockIdempotent", function(kg)
local b, Emb, k, g ;
    k := LeftActingDomain(kg);
    g := UnderlyingMagma(kg);
    Emb := Embedding(g,kg);
    for b in BlockDecomposition(kg).idempotents do
        if IsPrincipalBlockIdempotent(b,kg) then 
            return b;
        fi;
    od;
    return fail;

    # return Filtered(BlockIdempotentsOfGroupAlgebra(g, kg), b->IsPrincipalBlockIdempotent(b,kg) ); # old ver
end);


# args
# <b> : a block idempotent of <kg>
# <q> : a p-subgroup of <g>
# <kg> : a group algebra
# return 
#   the list of blocks <eq> of k<cgq> appearing the decomposition of br_{q}(b)
InstallGlobalFunction("DecompositionBlockImageUnderBrauerMorphism", function(b,q,kg)
    local g,cgq, cgqBl, brq, kcgq, emb, tmp;  
    g := UnderlyingMagma(kg); 
    cgq := Centralizer(g,q);
    emb := Embedding(g,kg);
    kcgq := Subalgebra(kg, List(cgq, x->x^emb));
    cgqBl := BlockDecompositionInSubgroupRing( kcgq, cgq ).idempotents;
    brq := BrauerMorphismOfGroupAlgebra(g,q,kg);
    return Filtered( cgqBl, eq -> not IsZero((b^brq)*eq) ); # the list of blocks <eq> of k<cgq> appearing the decomposition of br_{q}(b)
end);


# args
# <b> : a block idempotent of <kg>
# <d> : a defect group of <b>
# <kg> : a group algebra
# return 
#   return true  (if b is a principal type block),
#   return false (else)
InstallGlobalFunction("IsPrincipalTypeBlockIdempotent", function(b,d,kg)
    local q,g;
    g := UnderlyingMagma(kg);
    
    for q in ConjugacyClassesSubgroupsOfFixedSubgroup(g,d) do
        q := Representative(q);
        if Size(DecompositionBlockImageUnderBrauerMorphism(b,q,kg)) <> 1 then 
            return false;
        fi;
    od;
    return true;
end);


InstallGlobalFunction("FullDefectBlocksOfGroupAlgebra", function(kg)
local p, syl, bl, def, fullDefIndexes, k,g;
    k := LeftActingDomain(kg);
    g := UnderlyingMagma(kg);
    p := Size(PrimeField(k));
    syl := SylowSubgroup(g,p);
    bl := BlockIdempotentsOfGroupAlgebra(kg); # all blocks of kg
    # def := List( bl , b -> DefectClassOfBlockOfGroupAlgebra(b,kg) );# defect groups correspondence bl
    def := List( bl , b -> Representative(DefectClassOfBlockOfGroupAlgebra(b,kg) ));# defect groups correspondence bl
    fullDefIndexes := Filtered( [1..Size(def)] , i-> Order(def[i]) = Order(syl) ); # chose indexes of full defectgp

    return List(fullDefIndexes, i->bl[i]);
end);
# _FullDefectBlocksOfGroupAlgebra := function(kg)
# local p, syl, bl, def, fullDefIndexes, k,g;
#     k := LeftActingDomain(kg);
#     g := UnderlyingMagma(kg);
#     p := Size(PrimeField(k));
#     syl := SylowSubgroup(g,p);
#     bl := BlockIdempotentsOfGroupAlgebra(kg); # all blocks of kg
#     # def := List( bl , b -> DefectClassOfBlockOfGroupAlgebra(b,kg) );# defect groups correspondence bl
#     def := List( bl , b -> Representative(DefectClassOfBlockOfGroupAlgebra(b,kg) ));# defect groups correspondence bl
#     fullDefIndexes := Filtered( [1..Size(def)] , i-> Order(def[i]) = Order(syl) ); # chose indexes of full defectgp

#     return List(fullDefIndexes, i->bl[i]);
# end;
# FullDefectBlocksOfGroupAlgebra := function(args...)
#     local kg;
#     if Size(args) = 1 then 
#         kg := args[1];

#     elif Size(args) = 2 then # old ver
#         # g := args[1];
#         kg := args[2];
#     else 
#         Error("Different size of <args>. -----------------\n");
#     fi;

#     return _FullDefectBlocksOfGroupAlgebra(kg);
# end;


InstallGlobalFunction("BlockIdempotentsOfGroupAlgebraWithModules", function(kg)
    return BlockDecomposition(kg);
end);


# Construct a block idempotent <b> as sum of pim idempotents lying <b>.
InstallGlobalFunction("BlockIdempotentsOfGroupAlgebraSumOfPims", function(kg)
    local dec, irrs, cartan, mods, irrClasses, IsLyingSameBlockPims, IsLyingSameBlockIrrs, idemClasses, blocks , k, g, pairs;

    k := LeftActingDomain(kg);
    g := UnderlyingMagma(kg);

    # modules
    dec := PrimitiveDecomposition( One(kg), kg );
    mods := List(dec.indecomposition,x->x[2]);
    # irrs := CompleteSetRepresentatives( Classification( List( mods , pim -> TopOfGModule(pim) ),  MTX.IsEquivalent ) ); # 
    irrs := CompleteSetRepresentatives( Classification( List( mods , pim -> TopOfGModule(pim) ),  IsIsomorphicGModules ) ); # 
    cartan := CartanMatrixOfGroupAlgebra(irrs,g,k);
    irrClasses := ClassificationIrreduciblesSameBlock(irrs, cartan); # in sameclass iff sameblock 

    # relations
    IsLyingSameBlockIrrs := _ClassificationToEquivalenceRelation( irrClasses , IsIsomorphicGModules ); # 
    IsLyingSameBlockPims := function(x,y)
        return IsLyingSameBlockIrrs( TopOfGModule(x) , TopOfGModule(y) );
    end;

    # idempotents
    pairs := List([1..Size(dec.idempotents)], i -> [dec.idempotents[i], dec.indecomposition[i]]);
    idemClasses := Classification( pairs, function(x,y) return IsLyingSameBlockPims(x[2][2],y[2][2]); end ); # pim idem classes
    idemClasses := List(idemClasses, x->List( x, y->y[1]  ) );
    blocks := List( idemClasses, Sum ); # block idempotents

    return blocks;
end);



# 
	# args = [ "v", "kg"(, "de" )]
	# 	v: list of block idempotents
	#	kg : group algebra
	# 	de : list of defect groups corresponding <v>
	# Return : a sort permutation list <pe> of <v>
	#	Where, v{pe} and de{pe} are sorted lists	
	# Reamrk : 
	#	<v>, <de> is nondestructive
InstallGlobalFunction("PermutationOfSortBlockIdempotents", function(args...)
	local v, kg, de, v2 , pe, t, f, i, rel, n, co_d, sz;

	# args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
		sz := Size(args);
		if sz in [2,3] then 
			v := args[1];
			kg := args[2];
			n := Size(v);
			
			if sz = 2 then 
				de := List([1..n], i->[0,0]);
			elif sz = 3 then 
				de := args[3];
			fi;
		else 
			Error("wrong number of arguments -----------------------------------\n");
		fi;
		Assert(0, Size(v) = Size(de));
	# <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

	
	if IsGroup(de[1]) then
		co_d := List(de, i->IdSmallGroup(i)); # IdSmallGroup(i) : pair 
	fi;

	pe := [1..n];
	rel := function(i, j) return co_d[i] > co_d[j]; end; # pair として sort する
	Sort(pe, rel);

	v2 := [];
	f := false; # exist principal block
	for i in pe do
		if (not f) and IsPrincipalBlockIdempotent(v[i], kg) then 
			t := i;
			f := true;
		else 
			Add(v2, i);
		fi;
	od;

	pe := [];
	if f then Add(pe, t); fi; # t : principal block
	for i in v2 do Add(pe, i); od;

	return pe; # not inverse
end);
	

# 
	# Args :
	#	<bld> : a record of block decomposition with recnames 
	# 			["idempotents"(, "defectGroups")]
	# 	<kg>  : group algebra
InstallGlobalFunction("SortBlockDecomposition", function(bld, kg)
	local v,de,pe;
	
	v := bld.idempotents;
	if IsBound(bld.defectGroups) then 
		de := bld.defectGroups;
		pe := PermutationOfSortBlockIdempotents(v, kg, de);
	else 
		pe := PermutationOfSortBlockIdempotents(v, kg);
	fi;

	SortRecord(bld, pe);# not inverse
end);

