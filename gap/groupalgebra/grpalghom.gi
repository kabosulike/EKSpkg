# Args
#   <args> = [ <g>, <p>, <kg> ] or [ <p>, <kg> ],
#   <g> is a finite group,
#   <p> is a subgroup of <g>,
#   <kg> is the group algebra of <g> with coefficients in <k>.
InstallGlobalFunction("BrauerMorphismOfGroupAlgebra", function(args...)
    local k, cgp, e, cc, cce, ccsums, cgpe, kgp, kcgp, mat, i, o, g, p, kg;

    if Size(args) = 2 then
        p := args[1];
        kg := args[2];
        g := UnderlyingMagma(kg);
    elif Size(args) = 3 then
        g := args[1];
        p := args[2];
        kg := args[3];
    else  
        Error( "wrong number of arguments --------------------------\n");
    fi;
    
    # Parent algebra and its embedding
    k := LeftActingDomain(kg);
    e := Embedding(g, kg);

    # Basis for algebra
    cc := Orbits(p, Elements(g), function(g, p)
        return Inverse(p)*g*p;
    end);
    cce := List(cc, i -> List(i, g -> g^e));
    ccsums := List(cce, cc -> Sum(cc));
    cgpe := List(Centralizer(g, p), x -> x^e); #basis for kCg(P)

    # Subalgebras
    kgp := Subalgebra(kg, ccsums);
    kcgp := Subalgebra(kg, cgpe);

    # We calculate the Brauer morphism kG^P -> kCg(p).
    mat := NullMat(Dimension(kgp), Dimension(kcgp), k); # an empty list for representation matrix of Brauer morphism
    for i in [1..Length(cce)] do
        if Length(cce[i])=1 then
            o := Position(cgpe, cce[i][1]);
            mat[i][o] := One(k);
        fi;
    od;
    return LeftModuleHomomorphismByMatrix(Basis(kgp, ccsums), mat, Basis(kcgp, cgpe));
end);


InstallGlobalFunction("BrauerMorphismMatrixOfGroupAlgebra", function(g, p, kg)
    local k, cgp, e, cc, cce, ccsums, cgpe, kgp, kcgp, mat, i, o, b1, b2;
    # Parent algebra and its embedding
    k := LeftActingDomain(kg);
    e := Embedding(g, kg);

    # Basis for algebra
    cc := Orbits(p, Elements(g), function(g, p)
        return Inverse(p)*g*p;
        end);
    cce := List(cc, i -> List(i, g -> g^e));
    ccsums := List(cce, cc -> Sum(cc)); # basis for kG^P
    cgp:= Centralizer(g, p);
    cgpe := List(cgp, x -> x^e); #basis for kCg(P)

    # Subalgebras
    kgp := Subalgebra(kg, ccsums);
    kcgp := Subalgebra(kg, cgpe);

    # We calculate the Brauer morphism kG^P -> kCg(p).
    mat := NullMat(Dimension(kgp), Dimension(kcgp), k); # a null matrix for representation matrix of Brauer morphism
    for i in [1..Length(cce)] do
        if Length(cce[i])=1 then
            o := Position(cgpe, cce[i][1]);
            mat[i][o] := One(k);
        fi;
    od;

    return rec(
        matrix:= mat, 
        basisSource:= Basis(kgp),
        basisRange:= Basis(kcgp),
        );
end);


# args
#   <baS> , <baR> : basis of source, range
#   <mat> : a matrix 
#   <algS> , <algR> : source and range of <f>
#       where , <f> is a linar map corresponding <mat>
# 
# return 
#   true iff <f> is a algebra hom.
InstallGlobalFunction("IsAlgebraHomomorphismMatrixWithBasis", function(algS, mat, algR, baS, baR)
    local k,k2,vecAlgS, vecAlgR, vs,vr,
    rowX, rowY, rowXY, x, y , fx, fy, rowFXY, rowFXrowFY;
    
    k := LeftActingDomain(algS);
    k2 := LeftActingDomain(algR);
    if k <> k2 then 
        Error("---- LeftActingDomain of source and range are different.  ------\n");
    fi;

    # AsFullRowSpace
    vs := FullRowSpace(k,Dimension(algS));
    vr := FullRowSpace(k,Dimension(algR));
    for rowX in Basis(vs) do
        for rowY in Basis(vr) do
            x := LinearCombination( baS, rowX ); # in <algS>
            y := LinearCombination( baS, rowY ); # in <algS>
            rowXY := Coefficients( baS, x*y ); # in vectorspace of <algS>
            
            fx := LinearCombination( baR, rowX*mat ); # in <algR>
            fy := LinearCombination( baR, rowY*mat ); # in <algR>

            rowFXY := rowXY * mat;
            rowFXrowFY := Coefficients( baR, fx*fy );

            if rowFXY <> rowFXrowFY then 
                return false;
            fi;
            
        od;
    od;
    return true;
end);


InstallGlobalFunction("IsAlgebraHomomorphismMatrix", function(algS, mat, algR)
    # Use default basis
    return IsAlgebraHomomorphismMatrixWithBasis(algS, mat, algR, Basis(algS), Basis(algR) );    
end);


InstallGlobalFunction("IsBrauerCorrespondenceWithBrauerMorphism", function(b,c,br)
    return b^br = c^br;
end);


# <q> : common defetct group of <b> and <c>
InstallGlobalFunction("IsBrauerCorrespondence", function(b,c,q,kg)
    local br , g;
    g := UnderlyingMagma(kg);
    br := BrauerMorphismOfGroupAlgebra(g, q, kg);
    return IsBrauerCorrespondenceWithBrauerMorphism(b,c,br);
end);


# <g> , <h> : finite groups
# <module> : MTX-module
# return 
#   record which components are
#        basisS : basis of source ,
#        basisR : basis of Range,
#        repmat : representation matrix of <fh>.
#       
#   Where , 
#   f : kg -> End_k(<module>) : representation of <module>, 
#   fh : kg^h -> End_kh(<module>) : restriction of f , where 
#   kg^h is the subalgebra of kg s.t. the <h>-invaliant elements of kg.
InstallGlobalFunction("AlgebraHomomorphismMTXModuleRepresentationInvariant", function(g,h,module)
    local k,kg,endRing, emb, f , cc, cce, ccsums, veckgh, vecEndkh, basisEndkh, fh, 
    algebraS,algebraR, fh_mat;
    
    k := module.field;
    kg := GroupRing(k,g);
    endRing := MatrixAlgebra(k, module.dimension); # End_k(<module>)
    emb := Embedding(g,kg);
    f := AlgebraHomomorphismByImages(kg,endRing,List(GeneratorsOfGroup(g),x->x^emb),module.generators); 

    # Source : kg^h
    #   - Basis
    cc := Orbits(h, Elements(g), function(g, h)
        return Inverse(h)*g*h;
    end);
    cce := List(cc, i -> List(i, g -> g^emb));
    ccsums := List(cce, cc -> Sum(cc));
    #   - Vector space 
    veckgh := VectorSpace(k, ccsums); # source 

    # Range : End_kh(<module>)
    #   - Basis 
    basisEndkh := MTX.BasisModuleEndomorphisms(RestrictedGModule(g,h,module));
    vecEndkh := Subspace( endRing, basisEndkh );

    # matrix
    # fh : kg^h -> End_kh(<module>) , x -> f(x)
    fh_mat := MatrixRepresentationOfLinearMapByImages( Basis(veckgh), Basis( vecEndkh , basisEndkh ), List(ccsums, x->x^f) , k );
    
    
    # algebra hom
    algebraS := Subalgebra( kg, ccsums );           # algebra of source
    algebraR := Subalgebra( endRing, basisEndkh ) ; # algebra of range
    fh := AlgebraHomomorphismByImages( algebraS, algebraR, ccsums, List(ccsums,x->x^f) );
    
    return rec(
        basisS := Basis( veckgh ) , # basis of source 
        basisR := Basis( vecEndkh , basisEndkh ), # basis of Range
        repmat := fh_mat, # representation matrix
        hom := fh,
        
        algebraS := algebraS, # algebra of source
        algebraR := algebraR# algebra of range
        # endRing := endRing
        # rowSpaceS := FullRowSpace( k , Size(ccsums) ), # algebraS as full rowspace 
    );
end);