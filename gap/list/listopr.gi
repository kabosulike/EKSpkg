InstallGlobalFunction("RecursionClassification",function(list, ind, check , biRel)
    local connected, elm, i;
    
    connected := [];
    elm := list[ind];
    # check[ind] := true;   # if biRel is not satisfied with reflactive, this line add.

    for i in [1..Size(list)] do  
        if biRel(elm, list[i]) and check[i] <> true then  # remove checked elements
            Add(connected, i);
        fi;
    od;

    for i in connected do  
        check[i] := true;
        RecursionClassification(list, i, check, biRel );
    od;

end);


# arg 
#   list : list
#   biRel : binary relation 
# return 
#   Classification of list by eqRel.
#   (eqRel is equivalence relation generated by biRel)
InstallGlobalFunction("ClassificationByBinaryRelation", function(list, biRel)

    local  
        ans, # answer
        rem, # remainder
        class ,
        check, 
        rel, # binary relation satisfying refrective and symmetry
        i, tmp
    ;
    
    rem := list;# remainder
    ans := [];# answer

    if Size(rem) = 0 then  
        return ;
    fi;

    rel := function(x,y)
        if x = y then 
            return true; # satisfying reflective
        else
            return biRel(x,y) or biRel(y,x); # satisfying symmetry
        fi;
        # Remark : rel is a binary relation which is not requiered transitive.
    end;

    while Size(rem) <> 0 do
        check := List( [1..Size(rem)], i->false );
        RecursionClassification(rem, 1, check, rel);

        class := [];
        tmp := [];
        for i in [1..Size(check)] do 
            if check[i] = true then  
                Add(class, rem[i]);
            else 
                Add(tmp, rem[i]);
            fi; 
        od;

        rem := tmp;
        Add(ans, class);

    od;
    return ans;
end);


# arg
    # list : list 
    # equivRel : equivalence relation
# return 
    # list of list 
    #  s.t. classification of lst by equivRel.
InstallGlobalFunction("Classification", function(list, equivRel )


    local x , ans, rem, eqClass, i , lst;

    ans := [];
    lst := ShallowCopy(list);
    while not Size(lst) = 0 do
        x := lst[1];
        Remove(lst, 1);
        eqClass := [x];#equivalent class

        rem := [];
        if not Size(lst) = 0 then 
            for i in [1..Size(lst)] do
                if equivRel(lst[i] , x) then
                    Append(eqClass, [lst[i]] );
                else 
                    Append(rem, [lst[i]] );
                fi;
            od;
        fi;

        lst := rem;
        Append(ans, [eqClass]);
    od;
    return ans; #list of equivalent classes
end);


InstallGlobalFunction("ClassificationRepresentatives", function(list, equivRel)
    return CompleteSetRepresentatives( Classification(list, equivRel) );
end);

InstallGlobalFunction("_ClassificationToEquivalenceRelation", function(classes, eqRel)
    local biRel;
    biRel := function(x,y) 
        local pos;
        pos := PositionProperty(classes, c -> ElementInListEquivalenceRelation(c, x, eqRel) );
        if pos <> fail then 
            return ElementInListEquivalenceRelation(classes[pos], y, eqRel ); # true iff x and y in same class <classes[pos]>
        else 
            return fail;
        fi;
    end;
    return biRel;
end);


InstallGlobalFunction("ClassificationToEquivalenceRelation",function(args...)
    local classes, eqRel;
    
    if Size(args) = 2 then 
        classes := args[1];
        eqRel := args[2];
    elif Size(args) = 1 then 
        classes := args[1];
        eqRel := function(x,y) return x = y; end;
    else 
        Error("Wrong size of <args> ---------------------\n");
    fi;

    return _ClassificationToEquivalenceRelation(classes, eqRel);
    
end);



###############################################################################################
# Sort 
###############################################################################################
# Args
# <list> : a list 
# <func> : a order relation of <list>
# Return
#   the permutation of sort by <func> on <list>
# Remark :
#   <list> do not change after <PermutationOfSortFunction>.
InstallGlobalFunction("PermutationOfSortFunction",function(list, func)
    local list2, func2;

    list2 := [1..Size(list)];   # instead of <list1>
    func2 := function(a,b)      # order relation of <list2>
        return func(list[a],list[b]);        
    end;

    Sort(list2,func2);

    return list2;
end);


InstallGlobalFunction("IntersectionRelation", function(list1, list2, rel)
    local result, x, y;
    
    result := [];
    for x in list1 do
        for y in list2 do
            if rel(x,y) then 
                Add(result, x);     
            fi;
        od;
    od;
    return result;
end);
