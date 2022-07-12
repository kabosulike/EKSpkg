# Arg : <pe> is a permutation list 
#		(i.e.  a rearrangement of 1,2,...,n )
# Return : the inverse permutation of <pe>		
InstallGlobalFunction("InversePermutation", function(pe)
	local inv, n, i;
	
	n := Size(pe);
	inv := List([1..n], i-> -1);

	for i in [1..n] do
		inv[pe[i]] := i;
	od;
	return inv;
end);


# Args 
#   <re> : record
#   <perm> : permutation list 
# Return a sorted record <re>
#   a record <re> which components sorted by <perm>
InstallGlobalFunction("SortRecord",function(re, perm)
    local x;
    
    for x in RecNames( re ) do
        if IsList(re.(x)) and (not IsMatrix(re.(x))) then
            re.(x) := re.(x){perm};
        fi;
    od;
end);


InstallGlobalFunction("CheckSameFields", function( args... )
    local fields,i;

    fields := [];
    for i in [1..Size(args)] do
        if IsVectorSpace( args[i] ) then
            fields[i] := LeftActingDomain(args[i]);
        elif IsBound(args[i].isMTXModule) and args[i].isMTXModule then
            fields[i] := args[i].field;
        else 
            Error( "There is a element which is (not IsVectorSpace ) or (not IsMTXModule). ----------------------\n" );
        fi;
    od;

    if not CoincideElements( fields ) then
        Error("Do not coincide fields.-------------------------\n");
    fi;
end);


InstallGlobalFunction("Generators", function( a )
    
    if IsAlgebra(a) then 
        return GeneratorsOfAlgebra(a);
    elif IsGroup(a) then 
        return GeneratorsOfGroup(a);
    else 
        return fail;
    fi;
    
end);


# InstallGlobalFunction("IsOrthogonal", function(idemList)
#     local i,j;
#     if Size(idemList) = 1 then 
#         return true;
#     elif Size(idemList) = 0 then    
#         Print("Size(idemList) = 0 \n");
#         return true;
#     fi;

#     for i in [1..Size(idemList)-1] do 
#         for j in [i+1..Size(idemList)] do 
#             if not IsZero(idemList[i] * idemList[j]) then 
#                 return false;
#             fi;
#         od;
#     od;
#     return true;
# end;


InstallGlobalFunction("TopParent", function(obj)
    while HasParent(obj) do
        obj:= Parent(obj);
    od;
    return obj;
end);


InstallGlobalFunction("IsBoundComponentName", function(record)
    return IsBound(record.name);
end);


InstallGlobalFunction("InverseElement", function(x)
    return x^-1;    
end);


# Remark : not group hom
InstallGlobalFunction("MappingInverseElement", function( g, h )
    return MappingByFunction(g,h, x -> x^-1);
end);