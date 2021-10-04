H:=SL(2,8);
P:=SylowSubgroup(H,3);
elP:=Elements(P);
G:=PSL(2,8);
AuG:=AutomorphismGroup(G);
genAuG:=GeneratorsOfGroup(AuG);
# 2021/09/17試した時は2個目がきっちり位数３になった。
c:=genAuG[2];
C3:=Subgroup(AuG,[c]);
GstimeC3:=SemidirectProduct(C3,G);

irrkG:=IrreducibleGModules(G,k)[2];


LoadPackage("EKSPackage");
G:=SymmetricGroup(4);
p:=2;
AuG:=AutomorphismGroup(G);
m:=2;
k:=GF(p^m);
gen:=GeneratorsOfGroup(AuG);
Order(gen[1]);
c3:=gen[2];
C3:=Subgroup(AuG,[c3]);
tG:=SemidirectProduct(C3,G);
em1:=Embedding(tG,1);
em2:=Embedding(tG,2);
Size(Image(em1));
Size(Image(em2));
GG:=Image(em2);
regktG:=RegularModule(tG,k);
decregktG:=MTX.Indecomposition(regktG[2]);
irrktG:=IrreducibleGModules(G,k)[2];
PIMktG:=PrincipalIndecomposableModules(decregktG,irrktG);
FixedIrreduciblesRadicalLayerMultiplicities(PIMktG[1],irrktG);
# MTX.IsAbsolutelyIrreducible(module)

G:=SL(2,8);
PG:=PSL(2,8);
Generators
SaveWorkspace("aa.workspace");
LoadPackage()

LoadPackage("EKSpackage");
g:=PSL(2,8)
# 小平 充から皆様 (13:13)
g:=PSL(2,8);
k:=GF(3);
irr:=IrreducibleGModules(g,k);
P:=SylowSubgroup(g,3);
ngp:=Normalizer(g,P);
irrngp:=IrreducibleGModules(ngp,k);
regkngp:=RegularModule(ngp,k);
# decregngp:=MTX.Indecomposition(regkngp[2]);
# PIMktG:=PrincipalIndecomposableModules(decregngp[2],irrngp); bag
TopOfGModule(m);
PIMngp:=List([1,2],x->decregngp[x][2]);
FixedIrreduciblesRadicalLayerMultiplicities(PIMngp[1],irrngp[2]);

InducedGModule(g,ngp,PIMngp[1]);


LoadPackage("EKSPackage");
g:=SL(2,8);
geng:=GeneratorsOfGroup(g);
Display(geng[1]);
Display(geng[2]);
a1:=[[geng[1][1][1]^2,geng[1][1][2]^2],[geng[1][2][1]^2,geng[1][2][2]^2]];
# a2:=[[geng[2][1][1]^2,geng[2][1][2]^2],[geng[2][2][1]^2,geng[2][2][2]^2]];
a2:=[[geng[2][1][1]^2,geng[2][1][2]^2],[geng[2][2][1]^2,geng[2][2][2]^2]];

a:=[a1,a2];

Display(geng[1]);
Display(geng[2]);
Display(a1);
Display(a2);
c:=GroupHomomorphismByImages(g,g,geng,a);
Autg:=AutomorphismGroup(g);
c in Autg;
C:=Subgroup(Autg,[c]);
tG:=SemidirectProduct(C,g);
IsSubgroup(tg,g);
Size(Image(Embedding(tg,1)));
Size(Image(Embedding(tg,2)));
G:=Image(Embedding(tg,2));
IsSubgroup(tg,G);
sP:=SylowSubgroup(G,3);
nGsP:=Normalizer(G,sP);
ntGsP:=Normalizer(tG,sP);
k:=GF(3);
irrg:=IrreducibleGModules(g,k);
regkg:=RegularModule(g,k)[2];
