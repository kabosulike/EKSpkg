### notation
group := SymmetricGroup(4);
prime := 3;

ord_tbl := Irr(group);
br_tbl := Irr(group, prime);

### show 
Display(IsMatrix(ord_tbl)); # true 
Display(IsMatrix(br_tbl));	# true

Display(IsList(ord_tbl[1])); # true 
Display(IsList(br_tbl[1]));	# true

Display(ord_tbl); # show matrix
Display(br_tbl);	# show matrix
