# Memo : PadicValuation で代用可能．
InstallGlobalFunction("FixedPrimeRegularSingularPartInt", function(p, n)
    local i, a, r;
    a:=0;
    while(n mod p =0) do
        a:=a+1;
        n:=QuoInt(n,p);
    od;
    r:=rec(p:=p, p_part:=p^a, p_valuation:=a, p_prime_part:=n);
    return r;
end);