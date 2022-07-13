
InstallGlobalFunction("ForEach", function(list, func)
    local x;
    for x in list do 
        func(x);
    od;
end);


InstallGlobalFunction("Exist", function(list, func)
    return not ForAll(list, x -> not func(x));    
end);


InstallGlobalFunction("CoincideElements", function( list )
    local i, j ;

    if Size(list) <= 1 then 
        return true;
    fi;
    
    for i in [1..Size(list)] do
        for j in [i+1..Size(list)] do
            if list[i] <> list[j] then 
                return false;
            fi;
        od;
    od;
    return true;
end);


InstallGlobalFunction("_PrintList", function(list, isNewLine)
    local x, i;
    Print("[ ");
    for i in [1..Size(list)] do
        x := list[i];

        Print(x);
        if i <> Size(list) then 
            Print(", ");
        fi;
    od;
    Print(" ]");
    if isNewLine then 
        Print("\n");
    fi;
end);

InstallGlobalFunction("PrintList", function(args...)
    if Size(args) = 1 then 
        _PrintList(args[1], false);
    elif Size(args) = 2 then 
        _PrintList(args[1], args[2]);
    else 
        Error("wrong number of arguments ---------------------------\n");
    fi;
end);



InstallGlobalFunction("ShowListVertical",function(list)
    local x;
    for x in list do
        Print( x, "\n");
    od;
    Print("\n");
end);


InstallGlobalFunction("ShowListOfListTab",function(lst, tabnum)
    local x,t;
    for x in lst  do 
        for t in [1..tabnum] do 
            Print("\t");
        od; 
        Print(x,"\n");
    od;
end);


InstallGlobalFunction("ShowListOfList",function(lst)
    ShowListOfListTab(lst,0);
end);


InstallGlobalFunction("ElementInListEquivalenceRelation", function(list, x, eqRel)
    return Exist(list, y->eqRel(x,y));
end);


InstallGlobalFunction("CompleteSetRepresentatives", function(listOfList)
    # return List( [1..Size(listOfList)], i->listOfList[i][1]);
    return List( [1..Size(listOfList)], i-> Representative(listOfList[i]) );
end);



# <uniList> : universal list 
# <subList>     : sublist of <uniLst>
# <orderRel> : order relation (less than or equal)
# <prop>: property 
# return:  Upper bound of <subList> in <uniList>.
InstallGlobalFunction("UpperBoundOfOrderedList",function( uniList, subList, orderRel )
    local IsInUpperBound;
    IsInUpperBound := function(x)
        local list;
        ForAll( list , y -> orderRel(y,x) );
    end;
    
    return Filtered( uniList , subList , IsInUpperBound ); # UpperBound
end);


InstallGlobalFunction("UpperBoundOfOrderedListWithProperty",function( uniList, subList, orderRel , prop)
    local withProp;
    withProp := Filtered(uniList , prop);
    return Filtered( withProp , x -> ForAll( subList , y -> orderRel(y,x) ) ); # UpperBound
end);


InstallGlobalFunction("IsMaximalElementWithProperty",function( y , uniList, orderRel, prop )
    return prop(y) and ForAll( uniList, x -> (not orderRel(y,x)) or (y=x) or (not prop(x))); 
end);


InstallGlobalFunction("MaximalElementsWithProperty",function(uniList , orderRel, prop)
    local IsMaximalElementWithProperty_;
    IsMaximalElementWithProperty_ := function(y)
        return IsMaximalElementWithProperty(y, uniList, orderRel, prop);
    end;
    
    return Filtered(uniList,IsMaximalElementWithProperty_);
end);


InstallGlobalFunction("MinimalElementsWithProperty",function(uniList, orderedRel, prop)
    local dualRel;
    dualRel := function(x,y) return orderedRel(y,x); end; # dual relation
    return MaximalElementsWithProperty(uniList, dualRel, prop);
end);


# -------------------------------------------------
# <list> : list 
# <prop> : binary relation s.t. prop(a,b) is true iff a,b are identify.
# return 
#   true (if all elements of <list> are distinct ), 
#   false (otherwise).
InstallGlobalFunction("DistinctElementsProperty",function( list, prop )
    local i,j;
    for i in [1..Size(list)] do
        for j in [i+1..Size(list)] do
            if prop(list[i],list[j]) then
                return false;
            fi;
        od;
    od;
    return true;
end);


InstallGlobalFunction("DistinctElements",function( list )
    return DistinctElementsProperty(list, function(a,b) return a = b; end );
end);


# Args :
#   <largeList>, <smallList> : lists s.t. Size(<largeList>) >= Size(<smallList>)
#   <func> : a function return a value or return fail.
# Return :
#   Return a record.
#   
#   Check submultichoose <smallList> of <largeList>.
InstallGlobalFunction("SubmultichooseFunction",function( largeList , smallList , func )
    local rem , i, j, x, y, pos, values, success, remFlags, val, indices;

    if Size(largeList) < Size(smallList) then return fail; fi;

    remFlags := List( [1..Size(largeList)], i -> true ); # Remainder flags
    values   := [1..Size(smallList)];
    indices  := [1..Size(smallList)];
    for i in [1..Size(smallList)] do
        x := smallList[i];

        # calc <pos>
        success := false;
        for j in [1..Size(largeList)] do
            y := largeList[j];
            val := func(x,y);
            if remFlags[j] = true and val <> fail then 
                remFlags[j] := false;
                values[i]  := val;
                indices[i] := j;
                success := true;
                break;
            fi;
        od;

        if success = false then 
            return fail;
        fi;
    od;    

    return rec(
        values := values,
        indices := indices
    );
end);