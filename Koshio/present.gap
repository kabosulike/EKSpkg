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

S:=SuzukiGroup(32);
GeneratorsOfGroup(S);
Order(S);
A:=SylowSubgroup(S,5);
IsCyclic(A);
nsA:=Normalizer(S,A);
IrreducibleGModules(nsA,GF(5));

dec:=DecompositionMatrix(SL(2,8),3);
tbl:=CharacterTable("SL(2,8)");
tblm3:=CharacterTable("SL(2,8)",3) ;
dec:=DecompositionMatrix(tbl);
BlocksInfo(tbl,3);