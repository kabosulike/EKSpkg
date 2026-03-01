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

	# <module> の体が十分大きいとする．
	# arguments : 
	# 	<module> : MTX-module of <group>
	# 	<p_prime_element> : p'-element in <group>
	# return: 
	# 	<module> に対する Brauer character の <p_prime_element> における値
	public.BrauerCharacterOfGModule := function(group, module, p_prime_element)
		local MatrixRepresentationByGModule, representation, residue_field, quotient_field, prime, degree, br_char, eigen_value, eigen_values, _, pair, val, index; 

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

		# Brauer character
		br_char := Zero(quotient_field);
		eigen_values := private.Eigenvalues(residue_field, p_prime_element ^ representation);
		for eigen_value in eigen_values do
			index := private.PrimitiveElementIndex(residue_field, eigen_value);
			val := PrimitiveElement(quotient_field) ^ index;
			br_char := br_char + val;
		od;
		return br_char; 		

	end;

	return public;
end;
## Debug >>>>>>>>>>>>>>>>>>>>>> 
	# # group := AlternatingGroup(5); # p = 2, degree = 4 で OK 
	# group := SL(2,3); # p = 2, degree = 4 で OK 
	# prime := 2;
	# degree := 4;
	# field := GF(prime, degree);

	# for irr in IrreducibleModules(group, field)[2] do
	# 	### A5
	# 	# br_char := BrChar().BrauerCharacterOfGModule(group, irr, ());
	# 	# br_char := BrChar().BrauerCharacterOfGModule(group, irr, (1,2,3,4,5));
	# 	# br_char := BrChar().BrauerCharacterOfGModule(group, irr, (3,1,4,2,5));
		
	# 	### SL(2,3)
	# 	# br_char := BrChar().BrauerCharacterOfGModule(group, irr, [[1,0],[0,1]]*One(GF(3,1)));
	# 	br_char := BrChar().BrauerCharacterOfGModule(group, irr, [[1,1],[0,1]]*One(GF(3,1)));
	# 	# br_char := BrChar().BrauerCharacterOfGModule(group, irr, ([[1,1],[0,1]]*One(GF(3,1)))^(-1));

	# 	Display(br_char);
	# od;
## end Debug <<<<<<<<<<<<<<<<<<< 
