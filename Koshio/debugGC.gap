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