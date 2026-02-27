# x in <residue_field>
# Return : <quotient_field> における x の lifting element 
# Description: <resideu_field> の元 x を，mod p^degree の精度で quotient_field に持ち上げる．
# Note: n を小さくする事で，高速化の余地は残っている．
LiftingNewtonMethod := function(quotient_field, residue_field, x)
	local zeta, Lift, q, d, a, fa, ga, n, degree, DegreeFiniteField, prime, PowerInt, i;

	if(x = Zero(residue_field)) then return Zero(quotient_field); fi;

	zeta := PrimitiveElement(quotient_field);
	Lift := function(y) # y <> 0
		local alpha, e;
		
		alpha := PrimitiveElement(residue_field);
		for e in [1..Size(residue_field)-1] do
			if(alpha = y) then return zeta ^ e; fi;
			
			alpha := alpha * PrimitiveElement(residue_field);
		od;

		Assert(0, false);
		return fail;
	end;

	DegreeFiniteField := function(finite_field)
		local e, prime, prime_e;
		
		prime := Characteristic(finite_field);
		prime_e := Size(finite_field); # prime^e

		e := 0;
		while prime_e > 1 do 
			prime_e := QUO_INT(prime_e, prime);
			e := e + 1;
		od;
		return e;
	end;
	
	# Args: a, e は自然数
	# Rerturn: 冪 a^e
	PowerInt := function(a, e)
		local ans, pow; 
		
		if(e = 0) then return 1; fi;

		ans := 1;
		pow := a; # a^(2^i)
		while e > 0 do 
			if(e mod 2 = 1) then 
				ans := ans * pow;
			fi;

			e := QuoInt(e, 2);
			pow := pow * pow; 
		od;
		return ans;
	end;
	
	# constant
	prime := Characteristic(residue_field);
	q := prime; # power of prime
	degree := DegreeFiniteField(residue_field);
	Assert(0, prime^degree = Size(residue_field));
	n := q - 1;

	# init
	d := 1;
	a := -1; # lift of x in Z
	for i in [1..prime-1] do
		if i * One(residue_field) = x then 
			a := i; 
			break;
		fi; 
	od;
	Assert(0, a > 0);
	# calc
	while d < degree do 
		q := q * q;
		d := 2 * d;
		if q > Size(residue_field) then q := Size(residue_field); fi;

		fa := PowerInt(a, n) - 1;
		ga := n * PowerInt(a, n-1); # derivative of f
		Assert(0, ga mod q <> 0);
		a := a - fa * ((1/ga) mod q);
		a := a mod q;
	od;
	return a; # (lift of x) in Z[zeta] \subset Q(zeta) = <quotient_field>
end;

# Return: 
# 	<quotient_field> = Q(zeta_{<q>-1})
# 	<residue_field> = GF(<q>)
# ここで，<q> = <prime>^<degree>．
PModularSystem := function(prime, degree)
	local q, quotient_field, residue_field;
	
	q := prime ^ degree;
	quotient_field := CyclotomicField(q - 1); 
	residue_field := GF(q); 
	
	## alpha の 自然な lift が zeta 
	# zeta := PrimitiveElement(quotient_field);
	# alpha := PrimitiveElement(residue_field);

	return [quotient_field, residue_field];
end;
## Debug >>>>>>>>>>>>>>>>>>>>>> 
	# ### Lifting 
	# prime := 7; degree := 5;
	# pmod := PModularSystem(prime, degree);
	# quotient_field := pmod[1];
	# residue_field := pmod[2];

	# for i in [0..prime-1] do
	# 	x := One(residue_field) * i;
	# 	lift_x := LiftingNewtonMethod(quotient_field, residue_field, x);
		
	# 	Display([lift_x mod prime, lift_x]);
	# 	Print("\n");
	# od;
	
## end Debug <<<<<<<<<<<<<<<<<<< 