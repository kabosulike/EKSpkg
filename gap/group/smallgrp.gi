# =========================================================================
# arg 
# <g> : a finite group
# return 
#  true if <g> is a small group
#  false otherwise
InstallGlobalFunction("IsSmallGroup", function(g)
    return IdGroupsAvailable(Order(g));
end);


InstallGlobalFunction("AllSmallGroupsProperty", function(order, prop)
    return Filtered(AllSmallGroups(order), prop);
end);


# args:
#   <oList> : a list of order
#   <Prop> : a function argument (g,k) and  return true or false. 
#             Where, <g> is a group , <k> is a finite field.
#   <ChoseFiled> : a funcition argument (g,p) and return a finite field char p.
# return : 
#   a list of [g,k] , where <g> is a small group , <k> is a finite field 
#   satisfying <Prop>.
InstallGlobalFunction("AllSmallGroupsAndFiniteFieldGivenProperty", function(oList, Prop , ChoseField )
    local result, ord, p, k, g ;

    result := [];
    for ord in oList  do
        for g in AllSmallGroups(ord) do
            for p in PrimeDivisors(ord) do
                k := ChoseField(g,p);
                if Prop(g,k) then 
                    Add(result, [g,k]);
                fi;
            od;
        od;
    od;

    return result;
end);


# return 
#   a list of [ pair, k ] , where <pair> = [order, id] , <k> is a finite field.
InstallGlobalFunction("AllSmallGroupsIdAndFiniteFieldGivenProperty", function(oList, Prop, ChoseField)
    local gkList;
    gkList := AllSmallGroupsAndFiniteFieldGivenProperty(oList,Prop,ChoseField);
    return List(gkList, x->[IdSmallGroup(x[1]),x[2]] );
end);
# Debug >>>>>>>>>>>>>>>>>>>>>> 
# oList := [1..10];
# Prop := function(g,k) 
#     local airrs, irrs;
#     airrs := AbsolutIrreducibleModules(g,k,Order(g))[2];
#     irrs := IrreducibleModules(g,k,Order(g))[2];
#     return Size(airrs) = Size(irrs); 
# end;
# ChoseField := function(g,p)
#     return GF(p^2);    
# end;
# list1 := AllSmallGroupsAndFiniteFieldGivenProperty(oList, Prop, ChoseField);
# list2 := AllSmallGroupsIdAndFiniteFieldGivenProperty(oList, Prop, ChoseField);
# end Debug <<<<<<<<<<<<<<<<<<< 