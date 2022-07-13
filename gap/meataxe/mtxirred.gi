# args
#  args[1] =  <g> : a finite group
#  args[2] =  <p> : a prime number
#  (args[3] =  <dim> := 0 : max dimension of irreducible module)
# return 
#   record(
#       irreducibles,   # all irreducible modules
#       degree,
#       field   # GF(<p>^<degree>)
#   )
#   <degree> is degree of field extension s.t. 
#          (the number of absolutely irreducible modules with dimension less than or equal to <dim> )
#        = (the number of            irreducible modules with dimension less than or equal to <dim> )
InstallGlobalFunction("DegreeOfFieldExtensionAllAbsolutelyIrreducible", function(args...)
    local i,k,absIrr, irr, max, g,p,dim;

    g := args[1];
    p := args[2];
    if Size(args) = 2 then 
        dim := 0;
    elif Size(args) = 3 then 
        dim := args[3];
    else 
        Error("Wrong <args> size ----------------------\n");
    fi;

    max := 100;
    for i in [1..max]  do # i is degree
        k := GF(p^i);
        irr := IrreducibleGModules(g,k,dim);
        # absIrr := AbsolutelyIrreducibleModules(g,k,dim);

        if ForAll( irr[2], s -> MTX.IsAbsolutelyIrreducible(s) ) then 
        # if Size(absIrr[2]) = Size(irr[2]) then # ? 上の行の if となぜか結果が異なる. g = Alt(5), p = 2.
            return rec(
                # absIrreducibles := absIrr,
                irreducibles := irr,
                degree := i,
                field := k
            );
        fi;
    od;
    
    return fail;
end);


InstallGlobalFunction("FieldAllAbsolutelyIrreducible", function(args...)
    return DegreeOfFieldExtensionAllAbsolutelyIrreducible(args).field;
end);



# arg
#   <irrs> : a sorted list of irreducible modules. (ascending order of dimension)
# return
#   a list <irrNames> of string which is name of irreducible module.
#   i.e.    irrsNames[i] = (name of irr[i])
#
# Notation 
#   "triv" : trivial module
#   "Sn@" : simple , 
            #  n is dimension 
            #  @ は アルファベット a,b,c...
#   "Pn" : projective cover of Sn
#   "IMn" : n-dimension indecomposable module
# Memo
#   dual 案: 
#       △ dual の リストを作る
#       △ dual の 置換を記憶する
#   
#   採用
#       大文字，小文字で区別 (文字列だけで dual を判定できる． iso を判定する必要がなくなる)
#       dual の pair を返す関数を作る
#           self dual の module を M2a* のように書く．
#           self dual でないものは， 大文字と小文字で区別する
#       必要ならソートする？ しかし，ソートに意味があるとき，それを崩したくない．
# 案
#   MTX-module の record に
#       .name
#   の様な項目を追加する．
InstallGlobalFunction("IrreducibleNamesByDimension", function(irrs)
    local nextDim, irrNames, j, i, irr, irrName, alp;
	
	irrs := SortModules(irrs);

	nextDim := 0;
	irrNames := [];
	j := 0;
	for i in [1..Size(irrs)] do
		if IsTrivialGModule(irrs[i]) then 
			Add(irrNames, "k");
			continue;
		fi;

		if i < Size(irrs) then 
			nextDim := irrs[i+1].dimension;
		else
			nextDim := irrs[i].dimension + 1; # 形式的に決めたもの
		fi;

		irr := irrs[i];
		irrName := String(irr.dimension);

		alp := "";
		if irr.dimension = nextDim then 
			alp := [ CharInt( IntChar('a') + j ) ];
			j := j + 1;
		else
			if j > 0 then 
				alp := [ CharInt( IntChar('a') + j ) ];
			fi;
			j := 0;
		fi;
		irrName := Concatenation( "S" , irrName , alp ); # remark: char is not string.

		Add(irrNames, irrName);
	od;

	return irrNames;
end);



# Add 
#   .name components
InstallGlobalFunction("AddIrreducibleNamesByDimension", function(irrs)
    local irrNames, i;
    irrNames := IrreducibleNamesByDimension(irrs);
    for i in [1..Size(irrs)] do
        irrs[i].name := irrNames[i];
    od;
end);


# Args :
#   <args> = [ <g> , <k>(, <dim> ) ]
#   <g> : a finite group
#   <k> : a finite field 
#   <dim> : an integer
# Return:
#   It returns a list of representatives of the complete set of isomorphism classes of irreducible <g>-modules over <k>.
#
#   If <dim> is given,
#   then it returns the representatives whose dimension less than or equal to <dim>.  
InstallGlobalFunction("IrreducibleGModules", function(args...)
    local g,k,dim,irrs;

    g := args[1];
    k := args[2];        
    if Size(args) = 2 then 
        dim := 0;
    elif Size(args) = 3 then 
        dim := args[3];
    fi;

    irrs := List( MTX.CollectedFactors( RegularModule(g,k)[2] ), x -> x[1] );

    if dim > 0 then 
        irrs := Filtered( irrs, s -> s.dimension <= dim );
    fi;
    
    return [ GeneratorsOfGroup(g), irrs ];    
end);


