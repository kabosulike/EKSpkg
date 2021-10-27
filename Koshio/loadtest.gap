LoadPackage("EKSPackage");
p:=5;;
k:=GF(p);;
G:=SL(2,p);;
PG:=SylowSubgroup(G,p);;
H:=Normalizer(G,PG);;
regkG:=RegularModule(G,k)[2];;
decregkG:=MTX.Indecomposition(regkG);;
regkH:=RegularModule(H,k)[2];;
decregkH:=MTX.Indecomposition(regkH);;
irrskG:=IrreducibleGModules(G,k)[2];;
PIMskG:=PrincipalIndecomposableModules(decregkG,irrskG);;
irrskH:=IrreducibleGModules(H,k)[2];;
SortIrreducibleModulesTrivialModuleFirst(irrskH);;
PIMskH:=PrincipalIndecomposableModules(decregkH,irrskH);;
SaveWorkspace("SL2F5.gapsession");
# セーブされる場所はターミナルを開いた箇所。場所の指定はできないんだろうか？
# 一瞬で計算結果ごと再現できた。自分が作ったセッションを他の人が使えるかは疑問である。実行環境が違うんだから。
# もし計算結果を共有したいなら仮想マシン上で動かして仮想マシンごと共有するべき？
# Terminalに gap -L （SL2F5.gapsession）　を渡す。絶対パスである必要があるかもしれないけど。
# 相対パスでも良かった。素晴らしい。ちなみに、セーブデータはアホみたいに重たかった。６４MB とかあった。