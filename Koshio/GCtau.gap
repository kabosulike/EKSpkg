LoadPackage("EKSPackage");
_ProjectiveCoverOfGModule := function(m, pims, irrs)
# Remark : pims , irrs are sorted s.t. pims[i] is a projective cover of irrs[i] (for all i).
    local top , topMlty, tmp, i;

    if Size(pims) <> Size(irrs) then 
        Error("Size(pims) <> Size(irrs) -------------------\n");
    fi;

    top := TopOfGModule(m);    
    topMlty := FixedIrreduciblesCompositionFactorsMultiplicity( top ,irrs ); # list of multiplicity of top as irr modules
    
    tmp := []; # list of direct sum of pims 
    for i in [1..Size(irrs)] do
        if topMlty[i] <> 0 then 
           Add( tmp, MTX.DirectSum( pims[i] , topMlty[i] ) ); 
        fi;
    od;

    return MTX.DirectSum( tmp );
end;
# <G>: a group
# <Y>,<Z>: sets of subgroups of <G>

_Somecontained:=function(G,Y,Z)
    local y,z;
    for y in Y do
        for z in Z do
            if IsSubgroup(z,y)  then
                return true;
            fi;
        od;
    od;
    return false;
end;

GreenLocalSystem:=function(G,Q,H,p)
    local xG, yH, zG, zH, NGQ, QG, QH, elQG, fs,pccsubG, pccsubH;
    NGQ:=Normalizer(G,Q);
    if not IsSubgroup(H,NGQ) then
        Error("LocalSub doesn't contain Normalizer.\n");
    fi;
    QG:=ConjugacyClassSubgroups(G,Q);
    QH:=ConjugacyClassSubgroups(H,Q);
    elQG:=Elements(QG);
    fs:=Filtered(elQG,a->not RepresentativeAction(G,Q,a) in H);
    xG:=Set(fs,i->AsSubgroup(G,Intersection(Q,i)));
    yH:=Set(fs,i->AsSubgroup(H,Intersection(H,i)));
    pccsubG:=ModularConjugacyClassesSubgroups(G,p);
    pccsubH:=ModularConjugacyClassesSubgroups(H,p);

    zG:=Filtered(pccsubG,i->not(_Somecontained(G,Elements(i),xG)));
    zH:=Filtered(pccsubH,i->not(_Somecontained(H,Elements(i),yH)));
    return rec(x_conjGlobal:=xG,y_conjLocal:=yH,z_conjGlobal:=zG,z_conjLocal:=zH);
end;
# #debug 
g:=SymmetricGroup(5);
Ps:=SylowSubgroup(g,2);
NgPs:=Normalizer(g,Ps);
h:=SymmetricGroup(4);
IsSubgroup(g,h);
IsSubgroup(h,NgPs);
pccsubG:=ModularConjClassSubGroups(g,2);
pccsubH:=ModularConjClassSubGroups(h,2);
gls:=GreenLocalSystem(g,Ps,h,2);

GreenCorrespondenceGlobalToLocalFixedzG:=function(G,H,m,zG)
    local vtxm,Hm,decompHm,vtxHm,i;
    vtxm:=VertexClass(G,m);
    if not vtxm in zG then
        Error("Vertex not in z\n"); # ? vertex = 1 のときに,このエラーが出るかも
    fi;
    Hm:=RestrictedGModule(G,H,m);
    decompHm:=MTX.Indecomposition(Hm);
    vtxHm:=List(decompHm,x->VertexClass(H,x[2]));
    for i in [1..Length(decompHm)] do
        if Representative(vtxHm[i]) in vtxm then #永尾津島p251補題4.1による。
            return [vtxHm[i],decompHm[i][2]];    
        fi;
    od;
    return fail;
end;

_GreenCorrespondenceLocalToGlobalFixedzH:=function(G,H,m,zH)
    local vtxm,Gm,decompGm,vtxGm,i;
    vtxm:=VertexClass(H,m);
    if  not vtxm in zH then
        Error("Vertex not in z\n");
    fi;
    Gm:=InducedGModule(G,H,m);
    decompGm:=MTX.Indecomposition(Gm);
    vtxGm:=List(decompGm,x->VertexClass(G,x[2]));
    for i in [1..Length(decompGm)] do
        if vtxm[1] in vtxGm[i] then
            return [vtxGm[i],decompGm[i][2]];    
        fi;
    od;
    return fail;
end;


# args[1] = G,
# args[2] = Q,
# args[3] = H,
# (args[4] = p) 省略可
GreenCorrespondence:=function(G,Q,H)
    local gls,ltg,gtl, p, primes;

    # G := args[1];
    # Q := args[2];
    # H := args[3];
    primes := PrimeDivisors( Order(Q) );
    
    if Size(primes) > 1 then 
        Error("<Q> is not p-group ------------------\n");
    elif Size(primes) = 0 then
        Error("<Q> = 1 ------------\n");
    fi;

    # if Size(args) = 3 then 
        if Size(primes) = 1 then 
            p := primes[1];
        # else # case <Q> = 1

        #     # If <Q> = 1, then args[4] cannot be omitted.
        #     # Error("<Q> = 1 and <p> is not given. ----------------\n");

        fi;
    # elif Size(args) = 4 then 
    #     p := args[4];
    # else 
    #     Error("Size(args) wrong -----------------\n");
    # fi;
    
    gls:=GreenLocalSystem(G,Q,H,p);
    ltg:=function(m)
        return GreenCorrespondenceLocalToGlobalFixedzH(G, H, m, gls.z_conjLocal);
    end;
    gtl:=function(m)
        return GreenCorrespondenceGlobalToLocalFixedzG(G, H, m, gls.z_conjGlobal);
    end;

    return rec(LocalSystem:=gls,LocalToGlobal:=ltg,GlobalToLocal:=gtl);
end;
#debug 
G:=AlternatingGroup(5);
p:=2;
Ps:=SylowSubgroup(G,p);
# Ps := TrivialSubgroup(G);
H:=Normalizer(G,Ps);
k:=GF(p^2);
irrkG:=IrreducibleGModules(G,k)[2];;
irrkH:=IrreducibleGModules(H,k)[2];;
f:=GreenCorrespondence(G,Ps,H);
Print(f.LocalSystem);
f.GlobalToLocal(irrkG[1]);
f.LocalToGlobal(irrkH[1]);
MTX.IsomorphismModules(last,irrkG[3]);



MTX.IsIsomorphic;


FixedIrreduciblesRadicalLayerMultiplicities(f.LocalToGlobal(irrkH[1])[2],irrkG);

# -------------------------------------
LoadPackage("EKSPackage");;
p:=5;;
k:=GF(p);;
G:=SL(2,p);;
PG:=SylowSubgroup(G,p);;
H:=Normalizer(G,PG);;
irrkG:=IrreducibleGModules(G,k)[2];;
irrkH:=IrreducibleGModules(H,k)[2];;
f:=GreenCorrespondence(G,PG,H);;
List(irrkG{[1..4]},x->MTX.IsIsomorphic(x,f.LocalToGlobal(f.GlobalToLocal(x)[2])[2]));
List(irrkH,x->MTX.IsIsomorphic(x,f.GlobalToLocal(f.LocalToGlobal(x)[2])[2]));



f.LocalToGlobal(f.GlobalToLocal(irrkG[3])[2])[2];
# gls:=GreenLocalSystem(G,PG,NGPG,p);
# H:=NGPG;
MTX.IsIsomorphic;
f.GlobalToLocal(irrkG[1]);
Print(f.LocalSystem);
vertecesirrkG:=List(irrkG,x->VertexClass(G,x));
f.LocalToGlobal(irrkG[1]);
FixedIrreduciblesRadicalLayerMultiplicities(last,irrkG);

# <field>: finite field
# <dim>: a dimention of a vector space V
# <subgens>: a generator set of a subspace W of the vector space
# return: the matrix corresponding to the quotient map V->V/W
# If <Length(subgens)=0> then <field> and <dim> can't be read from <subgens>.

# SubspaceQuotientMatrix:=function(field,dim,subgens)
#     local extbasis,modulo,subdim;
#     if Length(subgens)=0 then
#         return ImmutableMatrix(field,IdentityMat(dim,field));
#     fi;
#         subdim:=RankMat(subgens);
#         extbasis:=ExtendToBasis(subgens);
#         modulo:=NullMat(subdim,dim-subdim,field);
#         Append(modulo,IdentityMat(dim-subdim,field));
#         modulo:=extbasis^-1*modulo;
#     return ImmutableMatrix(field,modulo);
# end;

# <mats> : a list of matrices which have the same length of columns
# return : the horizontal jointed matrix of <mats> 
HorizontalJointedMats:=function(mats)
    local tmats;
    tmats:=List(mats,x->TransposedMat(x));
    return TransposedMat(Concatenation(tmats));
end;

# <m>: a GModule
# return: the maximum subspace of <m> acted trivialy by G
# BasisInvariantSubGModule()
InvActSub:=function(m)
    local d,equ,i,j,idm;
    d:=m.dimension;
    idm:=IdentityMat(d);
    equ:=HorizontalJointedMats(List(m.generators,x->x-idm));
    return NullspaceMat(equ);
end;

# U^*\otimes V \cong Hom(U,V)
TransTensorToMat:=function(dimU,dimV,one_one_tensor)
    local i,j,M;
    M:=[];
    for i in [1..dimU] do
        M[i]:=[];
        for j in [1..dimV] do
            M[i][j]:=one_one_tensor[(i-1)*dimV+j];
        od;
    od;
    return M;
end;

# <a>,<b>: natural numbers
# <abvec>: a vector whose length equals to <a><b>
# return: the (<a>,<b>)-matrix which is splited into by <abvec>  
SpritVectorIntoMatrix:=function(a,b,abvec)
    local i,j,M;
    M:=[];
    for i in [1..a] do
        M[i]:=[];
        for j in [1..b] do
            M[i][j]:=abvec[(i-1)*b+j];
        od;
    od;
    return M;
end;

# Hom(U,W)~(U* \otimes W)^G
AlternativeBasisModuleHomomorphisms:=function(m1,m2)
    local dualm1,dualm1tensorm2,inv;
    dualm1:=DualGModule(m1);
    dualm1tensorm2:=TensorProductGModule(dualm1,m2);
    inv:=InvActSub(dualm1tensorm2);
    return List(inv,x->TransTensorToMat(m1.dimension,m2.dimension,x));
end;


MTX_ProjectiveCoverMatrix:=function(m,PIMs,irrs)
    local i,j,k,Maximals,basisHom,component,componentsmat,quot;
    Maximals:=List(irrs,x->MaximalSubGModules(x,m));
    componentsmat:=[];
    component:=[];
    for i in [1..Length(irrs)] do
        componentsmat[i]:=[];
        basisHom:=AlternativeBasisModuleHomomorphisms(PIMs[i],m);
        for j in [1..Length(Maximals[i])] do
                quot:=SubSpaceQuotientMatrix(Maximals[i][j],m.dimension,m.field);#SubSpaceQuotientMatrix:=function(subbasis,supdim,field)
                k:=1;
                while basisHom[k]*quot=Zero(basisHom[k]*quot) do
                    k:=k+1;
                od;
                Add(componentsmat[i],basisHom[k]);
                Remove(basisHom,k);
        od;
    od;
    return Concatenation(Concatenation(componentsmat));
end;

MTX_SyzygyOfGModule:=function(m,PIMs,irrs)
    local pcm,Pcm;
    Pcm:=_ProjectiveCoverOfGModule(m,PIMs,irrs);
    if Pcm.dimension=m.dimension then
        return "Zero GModule";
    fi;
    pcm:=MTX_ProjectiveCoverMatrix(m,PIMs,irrs);
    
    return MTX.InducedActionSubmodule(Pcm,NullspaceMat(pcm));
end;

ARTranslationOfGModule:=function(m,PIMs,irrs)
    local syzygy;
    syzygy:=MTX_SyzygyOfGModule(m,PIMs,irrs);
    if syzygy="Zero GModule" then
        return "Zero GModule";
    fi;
    return MTX_SyzygyOfGModule(syzygy,PIMs,irrs);
end;
IsTauRigidGModule:=function(m,PIMs,irrs)
local taum;
taum:=ARTranslationOfGModule(m,PIMs,irrs);
if taum="Zero GModule" then
    return true;
fi;
    return Length(AlternativeBasisModuleHomomorphisms(m,taum))=0;
end;

IsSupportTauTiltingGModule:=function(m,PIMs,irrs)
local vert,s;
    if not IsTauRigidGModule(m,PIMs,irrs)  then
        return false;
    fi;
    vert:=Length(MTX.HomogeneousComponents(m));
    s:=Length(MTX.CollectedFactors(m));
    return vert=s;
end;