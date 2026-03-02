BrChar := function()
	local 
		private, 
		public;
	
	private := rec();
	public := rec();

### private ### 

	# args 
	# 	a : 元
	# 	e : 自然数
	# 	unit : 積の単位元
	# return : 冪 a^e
	private.Power := function(a, e, unit)
		local pow, ans;

		Assert(0, e >= 0);
		if e = 0 then return unit; fi;
		
		pow := a; # a^(2^i)
		ans := unit;
		while e > 0 do 
			if e mod 2 = 1 then 
				ans := ans * pow;
			fi;
			
			pow := pow * pow; 
			e := QuoInt(e, 2);
		od; 

		return ans;
	end;

	# arguments : 
	# 	<finite_field> : size が <prime>^<degree> の有限体
	# return : <degree>
	private.DegreeOfFiniteField := function(finite_field)
		local prime, size, pow, index, ok, ng, mid;

		size := Size(finite_field);
		prime := Characteristic(finite_field);
		
		pow := prime; 
		index := 1;
		while pow < size do 
			pow := pow * pow; 
			index := index * 2;
		od;

		ok := index; ng := 0; 
		while ok - ng > 1 do 
			mid := QuoInt(ok + ng, 2);
			if private.Power(prime, mid, 1) >= size then ok := mid; 
			else ng := mid; 
			fi; 
		od;

		return ok;
	end;

	# arguments: 
	# 	<finite_field> : 有限体
	# 	<element> : <finite_field> の非ゼロな元
	# return : 
	# 	primitive element <prim> に対して，
	# 	<element> = <prim> ^ <index> となる最小の自然数 <index>
	private.PrimitiveElementIndex := function(finite_field, element)
		local prim, pow_prim, index_pow;
		Assert(0, element <> Zero(finite_field));
		# Assert(0, element in finite_field);

		if element = One(finite_field) then return 0; fi;

		prim := PrimitiveElement(finite_field);
		pow_prim := prim;
		index_pow := 1;
		while true do 
			if pow_prim = element then return index_pow; fi;
			
			if pow_prim = One(finite_field) then break; fi;
			pow_prim := pow_prim * prim;
			index_pow := index_pow + 1;
		od;
		
		Assert(0, false);
		return fail;
	end;
	
	# arguments : 
	# 	<field> : <matrix> の固有方程式の根を全て含む体
	# 	<matrix> : <field> 上の行列
	# return :
	# 	重複込みの eigenvalues の list. 
	private.Eigenvalues := function(field, matrix)
		local pol, roots;
		
		pol := CharacteristicPolynomial(matrix);
		roots := RootsOfPolynomial(field, pol);
		Assert(0, Size(roots) = Size(matrix));
		return roots;
	end;

### public ### 

	# return : quotient field Q(zeta_{q-1})
	public.QuotientField := function(prime, degree)
		local q;
		q := prime ^ degree;
		return CyclotomicField(q - 1); 
	end;

	# return : residue field GF(q)
	public.ResidueField := function(prime, degree)
		local q; 
		q := prime ^ degree;
		return GF(q); 
	end;

	public.RegularClasses := function(group, prime)
		return Filtered(ConjugacyClasses(group), 
			i-> Order(Representative(i)) mod prime <> 0 
		);
	end;

	public.RegularClassesPositions := function(group, prime)
		return PositionsProperty(ConjugacyClasses(group), 
			i-> Order(Representative(i)) mod prime <> 0 
		);
	end;

	# <module> の体が十分大きいとする．
	# arguments : 
	# 	<module> : MTX-module of <group>
	# 	<regular_element> : p'-element in <group>
	# return: 
	# 	<module> に対する Brauer character の <regular_element> における値
	public.BrauerCharacterOfGModule := function(group, module, regular_element)
		local q, MatrixRepresentationByGModule, representation, residue_field, quotient_field, prime, degree, br_char, eigen_value, eigen_values, _, pair, val, index; 

		# make a matrix representation by a GModule 
		MatrixRepresentationByGModule := function(g, m)
			local gens; # generators of <g>

			if Size(GeneratorsOfGroup(g)) = 0 then 
					gens := [One(g)];
			else
					gens := GeneratorsOfGroup(g);
			fi;

			return GroupHomomorphismByImages(g, GL(m.dimension, m.field), gens, m.generators);
		end;

		# representation of <module>
		if IsBound(module.representation) then 
			representation := module.representation; 
		else 
			representation := MatrixRepresentationByGModule(group, module);
			if IsMutable(module) then module.representation := representation; fi;
		fi;
	
		# fields
		residue_field := module.field;
		prime := Characteristic(residue_field);
		degree := private.DegreeOfFiniteField(residue_field);
		quotient_field := public.QuotientField(prime, degree);
		q := Size(residue_field);

		# Brauer character
		br_char := Zero(quotient_field);
		eigen_values := private.Eigenvalues(residue_field, regular_element ^ representation);
		for eigen_value in eigen_values do
			index := private.PrimitiveElementIndex(residue_field, eigen_value);
			# index := LogFFE(eigen_value,  Z(q));
			val := PrimitiveElement(quotient_field) ^ index;
			# val := E(q-1) ^ index;
			br_char := br_char + val;
		od;
		return br_char; 		

	end;

	
	# <module> の体が十分大きいとする．
	# arguments : 
	# 	<module> : MTX-module of <group>
	# return: record <ans>
	# 	ans.regular_conjugacy_classes : p'-element を含む，<group> における共役類
	# 	ans.brauer_characters : <module> に対する Brauer character の各 <regular_conjugacy_classes> における値のリスト．
	public.BrauerCharactersOfGModule := function(group, module)
		local residue_field, quotient_field, prime, regular_conjugacies, brauer_characters, regular_element, degree;

		# fields
		residue_field := module.field;
		prime := Characteristic(residue_field);
		degree := private.DegreeOfFiniteField(residue_field);
		quotient_field := public.QuotientField(prime, degree);

		# conjugacy classes
		regular_conjugacies := public.RegularClasses(group, prime);

		# brauer characters
		brauer_characters := [];
		for regular_element in regular_conjugacies do
			regular_element := Representative(regular_element);
			Add(brauer_characters, public.BrauerCharacterOfGModule(group, module, regular_element));
		od;

		return brauer_characters;
	end;


	# <module> の体が十分大きいとする．
	# arguments : 
	# 	<module> : MTX-module of <group>
	# return: record <ans>
	# 	ans.regular_conjugacy_classes : p'-element を含む，<group> における共役類
	# 	ans.table : <module> に対する Brauer character table
	public.BrauerCharacterTableOfGModule := function(group, residue_field)
		local regular_conjugacies, brauer_character_table, irr, brauer_characters, regular_conjugacy_classes;

		# brauer character table
		brauer_character_table := [];
		for irr in IrreducibleModules(group, residue_field)[2] do
			brauer_characters := public.BrauerCharactersOfGModule(group, irr);
			Add(brauer_character_table, brauer_characters);
		od;
		
		return brauer_character_table; 
	end;
	
	# arguments : 
	# 	<ord_res> : ordinary character を <prime>-regular に制限した list
	# 	<brauer_table> : Brauer character table
	# 	ただし，conjugacy classes 順序は，単位元からなる class が先頭にあるとする．
	# return : 
	# 	<ord_res> を <brauer_table> で分解したときの係数の list を返す．
	public.Decomposition := function(ord_res, brauer_table)
		local coe, ord_res_dim, br_dims, DFS;
		
		coe := List([1..Size(brauer_table)], i -> 0 ); # coefficients
		ord_res_dim := ord_res[1];
		br_dims := List(brauer_table, br -> br[1]);

		DFS := function(index, depth)
			local d;

			if (depth = Size(brauer_table)) then 
				if(ord_res = Sum(List([1..Size(brauer_table)], i -> coe[i] * brauer_table[i]))) then return true;
				else return false; 
				fi;
			fi;

			
			for d in [0..QuoInt(ord_res_dim, br_dims[index])] do
				coe[index] := d;
				if(DFS(index + 1, depth + 1)) then return true; fi;
			od;
			
			return false;
		end;
		
		DFS(1, 0);
		
		return coe;
	end;

	# arguments : 
	# 	<group> : 有限群
	# 	<prime> : 素数
	# 	<ords> : <group> の ordinary character table 
	# 	<brauer_table> : Brauer character table 
	# 	ただし，conjugacy classes 順序は，単位元からなる class が先頭にあるとする．
	# return : 
	# 	<ords> を <brauer_table> で分解した，decomposition matrix を返す．
	public.DecompositionMatrix := function(group, prime, ords, brauer_table)
		local reg_pos, dec_mat, ord, dec_list;

		reg_pos := BrChar().RegularClassesPositions(group, prime);
		dec_mat := [];
		for ord in ords do
			dec_list := BrChar().Decomposition(ord{reg_pos}, brauer_table);
			Add(dec_mat, dec_list);
		od;
		
		return dec_mat;
	end;

	return public;
end;
## Debug >>>>>>>>>>>>>>>>>>>>>> 
	# group := AlternatingGroup(5); # p = 2, degree = 4 で OK 
	# # group := SL(2,3); # p = 2, degree = 4 で OK 
	# prime := 2;
	# degree := 4;
	# field := GF(prime, degree);
	# br_table := BrChar().BrauerCharacterTableOfGModule(group, field);

	# Display(group);
	# Display(br_table);

	# ### decomposition
	# dec_mat := BrChar().DecompositionMatrix(group, prime, Irr(group), br_table);
	# Display(dec_mat);

## end Debug <<<<<<<<<<<<<<<<<<< 