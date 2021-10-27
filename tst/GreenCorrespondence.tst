gap> p:=5;;
gap> g:=SL(2,p);;
gap> Pg:=SylowSubgroup(g,p);;
gap> NgPg:=Normalizer(g,Pg);;
gap> gls:=GreenLocalSystem(g,Pg,NgPg,p);;
gap> Length(gls.x)=1;
true