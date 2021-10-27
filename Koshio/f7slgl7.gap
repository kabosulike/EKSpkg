LoadPackage("EKSPackage");
p:=11;
k:=GF(p);
n:=2;
G:=SL(n,p);
tG:=GL(n,p);
regkG:=RegularModule(G,k);
regktG:=RegularModule(tG,k);
irrkG:=IrreducibleGModules(G,k)[2];
# irrktG:=IrreducibleGModules(tG,k)[2];
Length(irrkG);
# Length(irrktG);
# decregkG:=MTX.Indecomposition(regkG[2]);

# PIMkG:=PrincipalIndecomposableModules(decregkG,irrkG);

# おわんないからs7を7個直和したもので割ってから実行したほうがいいかも、埋め込み方がわかりません。内部直和の情報はポイントを知りたいわけではないから必要ないし。あと他には、忠実表現からPIMを出すアルゴリズムの実装と、あとGLのPIMはSLのPIMの誘導から全部得られるから安心.
# S7を準同型で埋め込んで割って、埋め込んで、割ってを繰り返して可能な限り取り除く。
# また、N G(P)の射影加群の誘導から射影加群を集めていけばいいのではないだろうか？そうすればもっとたくさん射影加群を取り除ける。
# ただし、単純射影的な場合と違って単射性なり全射性を考慮しなくてはならないことを注意する。これらはRankの計算で判別は容易であるためまだマシなトラブルと言える。
# MTX.CompositionFactors(reg);
# MTX.IsomorphismModules(module1,module2);

# B3:=MTX.DirectSum(irrkG[7],7);
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],regkG[2]);

inc:=homs[1]
# Sum(homs);
# MTX.InducedActionFactorModule(regkG,last);



fac:=regkG[2];;
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],fac);;
fac:=MTX.InducedActionFactorModule(fac,homs[1]);
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],fac);
fac:=MTX.InducedActionFactorModule(fac,homs[1]);
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],fac);
fac:=MTX.InducedActionFactorModule(fac,homs[1]);
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],fac);
fac:=MTX.InducedActionFactorModule(fac,homs[1]);
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],fac);
fac:=MTX.InducedActionFactorModule(fac,homs[1]);
homs:=MTX.BasisModuleHomomorphisms(irrkG[p],fac);
fac:=MTX.InducedActionFactorModule(fac,homs[1]);
# 繰り返して次元を可能な限り減らす。1199

dec:=MTX.Indecomposition(fac);
irrkGns:=List([1..p-1],x->irrkG[x]);

PIMkG:=PrincipalIndecomposableModules(dec,irrkGns);
Add(PIMkG,irrkG[p]);
# ここまでで一旦終わり
FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[1],irrkG);
FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[3],irrkG);
FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[5],irrkG);

FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[2],irrkG);
FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[4],irrkG);
FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[6],irrkG);
FixedIrreduciblesRadicalLayerMultiplicities(PIMkG[7],irrkG);
InducedGModule(tG,G,PIMkG[1]);
decktG:=List(PIMkG,x->MTX.Indecomposition(InducedGModule(tG,G,x)));
decktG:=Concatenation(decktG);
PIMktG:=PrincipalIndecomposableModules(decktG,irrktG);
listlayertG:=List(PIMktG,x->FixedIrreduciblesRadicalLayerMultiplicities(x,irrktG));