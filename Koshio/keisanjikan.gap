LoadPackage("EKSPackage");
g:=SymmetricGroup(5);
k:=GF(5);
rg:=RegularModule(g,k);

AlternativeBasisModuleHomomorphisms(rg[2],rg[2]);
MTX.BasisModuleHomomorphisms(rg[2],rg[2]);

AutomorphismGroup(g);genera