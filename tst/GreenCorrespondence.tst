gap> p:=5;;
gap> g:=SL(2,p);;
gap> Pg:=SylowSubgroup(g,p);;
gap> NgPg:=Normalizer(g,Pg);;
gap> gls:=GreenLocalSystem(g,Pg,NgPg,p);;
gap> Length(gls.x)=1;
true
gap> p:=5;;
gap> k:=GF(p);;
gap> PG:=SylowSubgroup(G,p);;
gap> H:=Normalizer(G,PG);;
gap> irrkG:=IrreducibleGModules(G,k)[2];;
gap> irrkH:=IrreducibleGModules(H,k)[2];;
gap> f:=GreenCorrespondence(G,PG,H);;
gap> List(irrkG{[1..4]},x->MTX.IsIsomorphic(x,f.LocalToGlobal(f.GlobalToLocal(x)[2])[2]));
[ true, true, true, true ]
gap> List(irrkH,x->MTX.IsIsomorphic(x,f.GlobalToLocal(f.LocalToGlobal(x)[2])[2]));
[ true, true, true, true ]