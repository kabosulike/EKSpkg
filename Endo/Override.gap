###############################################################################
# MakeReadWriteGlobal を用いて，read only の関数も上書き可能に出来る．
# Remark : 
#	MakeReadWriteGlobal( <name> ) を使うためには，
#	InstallGlobalFunction( <name>, <function> ) の <name> を，string にしておく．
# Example
#	DeclareGlobalFunction( "F" );
#	InstallGlobalFunction( "F", x -> x^2 );  # OK
#	# InstallGlobalFunction( F, x -> x^2 );  # NG
###############################################################################




# (1) 基本

	## Debug >>>>>>>>>>>>>>>>>>>>>> 
		# # 本来は, GaloisField は read only の関数だが，上書きする．

		# MakeReadWriteGlobal( "GaloisField" ); 
		# BIND_GLOBAL( "GaloisField",  function() Print( "GF\n" ); end);

		# GaloisField();
	## end Debug <<<<<<<<<<<<<<<<<<< 


# (2) 応用
	# InstallGlobalFunction 自体が read only だが，上書き可能にして定義しなおす．

	MakeReadWriteGlobal( "InstallGlobalFunction" ); 
	BIND_GLOBAL( "InstallGlobalFunction",  function( args... ) # InstallGlobalFunction で定義した関数が，上書き可能になるように，InstallGlobalFunction 自体を上書きする．
		local name, func;
		
		# args >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
			if not Size(args) in [2] then
				Error( "wrong number of arguments -------------------\n");
			fi;

			if Size(args) = 2 then
				name := args[1]; # a string of name of <func>
				func := args[2]; # function

				MakeReadWriteGlobal( name ); # 既存の read only 関数であっても，上書き可能にする．
				BIND_GLOBAL( name, func );

			fi;
		# <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< 
	end);

	## Debug >>>>>>>>>>>>>>>>>>>>>> 

		# # SylowSubgroup は，本来は read only だが，
		# # 上で InstallGlobalFunction を書き換えて，
		# # 上書き可能になった．
		# InstallGlobalFunction( "SylowSubgroup", function() Print("Sylow subgroup \n"); end );
		# InstallGlobalFunction( "Func", function() Print("Func \n"); end );

		# SylowSubgroup();
		# Func();

	## end Debug <<<<<<<<<<<<<<<<<<< 
