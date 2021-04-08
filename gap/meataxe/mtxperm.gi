InstallGlobalFunction("ScottModule", function(G,H,k)
    local a,deca,tG,tH,i,j,p,tops;
    p:=Characteristic(k);
    tG:=TrivialGModule(G,k);
    tH:=TrivialGModule(H,k);
    a:=InducedGModule(G,H,tH);
    deca:=MTX.Indecomposition(a);
    MTX.IsIrreducible(tG);
    for i in [1..Length(deca)] do
        tops:=MTX.CollectedFactors(TopOfGModule(deca[i][2]));
        for j in [1..Length(tops)] do
            if MTX.IsEquivalent(tG,tops[j][1]) then
                return deca[i][2];
            fi;
        od;
    od;
    return fail;
end);