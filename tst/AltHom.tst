gap> G:=SymmetricGroup(4);;
gap> p:=2;;
gap> k:=GF(2);;
gap> tG:=TrivialGModule(G,k);;
gap> regkG:=RegularModule(G,k)[2];;
gap> Mats:=[[[1,0],[0,1]],[[1,1,1],[1,0,1]]];;
gap> Display(Mats[1]);
[ [  1,  0 ],
  [  0,  1 ] ]
gap> Display(Mats[2]);
[ [  1,  1,  1 ],
  [  1,  0,  1 ] ]
gap> jMats:=HorizontalJointedMats(Mats);;
gap> Display(jMats);
[ [  1,  0,  1,  1,  1 ],
  [  0,  1,  1,  0,  1 ] ]
gap> v:=Concatenation(jMats);
[ 1, 0, 1, 1, 1, 0, 1, 1, 0, 1 ]
gap> SpritVactorIntoMatrix(2,5,v)=jMats;
true
gap> Length(AlternativeBasisModuleHomomorphisms(regkG,tG))=1;
true