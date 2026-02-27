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