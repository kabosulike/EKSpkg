# Test for GCtau
gap> p:=5;;
gap> k:=GF(p);;
gap> G:=SL(2,p);;
gap> PG:=SylowSubgroup(G,p);;
gap> H:=Normalizer(G,PG);;
gap> regkG:=RegularModule(G,k)[2];;
gap> decregkG:=MTX.Indecomposition(regkG);;
gap> regkH:=RegularModule(H,k)[2];;
gap> decregkH:=MTX.Indecomposition(regkH);;
gap> irrskG:=IrreducibleGModules(G,k)[2];;
gap> PIMskG:=PrincipalIndecomposableModules(decregkG,irrskG);;
gap> irrskH:=IrreducibleGModules(H,k)[2];;
gap> SortIrreducibleModulesTrivialModuleFirst(irrskH);;
gap> PIMskH:=PrincipalIndecomposableModules(decregkH,irrskH);;
gap> f:=GreenCorrespondence(G,PG,H,p);;
gap> GirrkG1:=f.GlobalToLocal(irrskG[1])[2];;
gap> OkG:=MTX_SyzygyOfGModule(irrskG[1],PIMskG,irrskG);;
gap> OkH:=MTX_SyzygyOfGModule(irrskH[1],PIMskH,irrskH);;
gap> GOkG:=f.GlobalToLocal(OkG)[2];;
gap> OOkG:=MTX_SyzygyOfGModule(OkG,PIMskG,irrskG);;
gap> OOkH:=MTX_SyzygyOfGModule(OkH,PIMskH,irrskH);;
gap> GOOkG:=f.GlobalToLocal(OOkG)[2];;
gap> MTX.IsIsomorphicGModules(GirrkG1,irrskH[1]);
true
gap> MTX.IsIsomorphicGModules(GOkG,OkH);
true
gap> MTX.IsIsomorphicGModules(GOOkG,OOkH);
true