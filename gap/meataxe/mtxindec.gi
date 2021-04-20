# -------------------------------------------------------
# <module> : MTX-module
# return 
# List <decM> of indecomposition of <module>. 
# decM[i] is a MTX-module for all i.
InstallGlobalFunction("IndecompositionGModuleList", function(module)
    local decM;

    CheckMTXModule(module);

    # indecomposition
    if IsBound(module.isIndecomposable) and module.isIndecomposable then 
        decM := [module];
    else
        decM := List(MTX.Indecomposition(module),x->x[2]);
    fi;
    return decM;
end);


# arg
# <dec> : indecomposition, list of [ matrix, module ]
# return
#   A list of the index numbers of the indecomposable compoments.
#   The index numbers are given by indecomposition <dec>,
#   that are in the homogeneous component.
InstallGlobalFunction("IndecompositionHomogeneousComponentsIndicesList", function( dec )
    local func,list, indicesList;

    if not IsList(dec) then
        Error( "not IsList(dec) ------------------\n");
    fi;

    if not IsMatrix(dec[1][1]) then 
        Error( " not IsMatrix(dec[1][1]) ------------------\n");
    elif not dec[1][2].isMTXModule then 
        Error( " not dec[1][2].isMTXModule ---------------------\n");
    fi;
    
    func := function(i, j)
        return MTX.IsomorphismModules( dec[i][2] , dec[j][2] ) <> fail; 
    end;
    list := [1..Size(dec)];
    indicesList := Classification( list , func );

    return indicesList;
end);


# args 
# q : a cyclic p-group
# k : a finite field char p
# return 
# All indecomposable kq-modules as MTX module, their sources, and vertices .
# Reference : Webb, exercises 11.6(a)
InstallGlobalFunction("AllIndecomposableGModulesOfCyclicPGroup", function( q , k )
# Remark : q is a cyclic p-group
    local subs, reg, radSer, m ,dim, p_part, ord, vtx, vtxClass2, src , p;

    if not IsCyclic(q)  then 
        Error(" <q> in not a cyclic group. --------------------- \n");
    fi;
    
    # Notation
    p := Size(PrimeField(k));    
    subs := AllSubgroups(q); # all (p-)subgroups
    
    # Module
    # reg : regular k<q>-module 
    if Order(q) = 1 then 
        # reg := GModuleByMats( [], 1 ,k ); # <reg> has generators [[[One(k)]]]
        reg := GModuleByMats([[[One(k)]]],k);
    else 
        reg := RegularModule(q,k)[2];
    fi;
    radSer:= RadicalSeries(reg).radicalSeries;
    radSer:= Concatenation( [reg] , radSer ); # containing rad^{0}
    for m in radSer do
        dim := m.dimension;
        p_part := FixedPrimeRegularSingularPartInt(p, dim).p_part; # p-part of <dim>
        ord := Order(q) / p_part; # order of a vertex of <m>
        vtx := Filtered( subs, x -> Order(x) = ord )[1]; # a vertex of <m>, (Ref [ Webb ])
        src := SourceOfGModule( q , m , vtx );

        # add record
        m.vertexClass := vtx^q;
        m.source := src;
    od;

    # chose representative of isomorphism classes
    radSer := Classification ( radSer, function(x,y) return MTX.IsomorphismModules(x,y)<>fail; end );
    radSer := List(radSer, Representative );

    return radSer; # add vertexClass and source
end);

# q : a p-group
# k : a finite field char p
InstallGlobalFunction("AllIndecomposableFullVertexGModulesOfCyclicPGroup", function( q, k )
    local list;
    list := AllIndecomposableGModulesOfCyclicPGroup(q,k);# indeclist. <list>[i] is a record containing .vertexClass and .source 
    return Filtered(list , x -> Order(q) = Order(Representative(x.vertexClass)) );
    # return Filtered(list , x -> q in x.vertexClass );
end);


# args
# g : a finite group
# q : a p-subgroup of <g>
# src : an indecomposable kq-module as MTX module with vertex <q>
# return 
#  list : <list>[i] is an indecomposable kg-module with vertex <q> and source <src>.
InstallGlobalFunction("AllIndecomposableGModulesFixedVertexSourcePair", function(g, q, src)
# Remark : don't check <src> has a vertex <q> as kq-module.
    local m, indecomp, list, smd, smd2, ans, tmp, br;


    m := InductionOfGModule( g, q, src );
    indecomp := List(MTX.Indecomposition(m), x->x[2] );
    tmp := Classification( indecomp , function(x,y) return MTX.IsomorphismModules(x,y)<>fail; end );
    list := List(tmp, Representative);

    ans := [];
    for smd in list do # <smd> are direct summand of indecued module
        smd2 := ShallowCopy( smd ); # mutable, kg-module
        # Remark :
        #   smd.vertexClass := q^g;# immutable
        #   smd.source := src;# immutable

        # add record
        br := BrauerMorphismOfEndRing(g,q,smd2);
        if q in VertexClass( g, smd2 ) then
        # i.e. if not IsZeroDimensionOfImage(br) then 
            # smd2.vertexClass := q^g; # mutable
            smd2.vertexGroup := q;# mutable
            smd2.source := src;# mutable
            Add(ans, smd2);
        fi;
    od;

    return ans;
end);





# <g> is a finitegroup,
# <k> is a finite field,
# This function calcurates the list of all indecomposable modules with cyclic vertex.
# This function returns a record.
InstallGlobalFunction("AllIndecomposableModulesCyclicVertex", function( g, k )
    local p, m, subs, ind, inds1, inds2, q, srcs, s, tmp1, decs, tmp2, result;

    p := Characteristic(k);
    subs := ModularConjugacyClassesSubgroups( g, p );
    subs := List( subs, Representative );
    subs := Filtered( subs, q -> IsCyclic(q)  );

    ind := 1;
    inds1 := [];
    inds2 := [];
    result := [];
    for q in subs  do
        srcs := AllIndecomposableFullVertexGModulesOfCyclicPGroup( q, k ); # source modules
        tmp1 := [];
        for s in srcs do
            # modules
            decs := AllIndecomposableGModulesFixedVertexSourcePair( g, q, s ); # all indecomposable modules with vertex source <q>,<s>
            for m in decs do
                m.sourceModule := s;
            od;
            Append( result , decs );

            # indices
            tmp2 := [ind..ind+Size(decs)-1];
            Add( inds2, tmp2 );
            Add( tmp1, tmp2 );
            ind := ind + Size(decs);
        od;

        Add( inds1, Concatenation(tmp1) );
    od;

    return rec(
        modules := result,
        # indicesVtx := inds1, indicesVertex := inds1, # list of indices classes same vertex group
        # indicesSrc := inds2,  indicesSource := inds2, # list of indices classes same source module
        indicesV := inds1, # list of indices classes same vertex group
        indicesS := inds2, # list of indices classes same source module
    );

end);



# --------------------------------------------------------
# Calc indecomposition and each vertex classes and multiplicity as direct summand.
# 
# args
#   <g> : a fininte group
#   <module> : a MTX kg-module 
# return 
#   record which components are
#       <indecomposables> : a list of representative iso classes of indec direct summand of <module>
#       <vertexClasses>   : a list of vertex classes of <indecomposables>
#       <multiplicities>  : a list of multiplicity of <indecomposables> in <module>
InstallGlobalFunction("IndecompositionOfGModuleAndVetexClasses", function(g, module)
    local hc, indecomposables;
    hc := MTX.HomogeneousComponents(module);
    indecomposables := List(hc, x->x.component[2] );
    return rec(
        indecomposables := indecomposables, # indec direct summand of module
        vertexClasses := List( indecomposables, smd->VertexClass(g,smd) ),
        multiplicities := List(hc, x->Size(x.indices) )
    );
end);

# --------------------------------------------------------
# Functions for "Green Correspondence"
# 
# <G>: a group
# <Y>,<Z>: sets of subgroups of <G>
InstallGlobalFunction("GroupSetsContaining",function(G,Y,Z)
    local y,z;
    for y in Y do
        for z in Z do
            if IsSubgroup(z,y)  then
                return true;
            fi;
        od;
    od;
    return false;
end);

InstallGlobalFunction("GreenLocalSystem",function(G,Q,H,p)
    local xG, yH, zG, zH, NGQ, QG, QH, elQG, fs,pccsubG, pccsubH;
    NGQ:=Normalizer(G,Q);
    if not IsSubgroup(H,NGQ) then
        Error("LocalSub doesn't contain Normalizer.\n");
    fi;
    QG:=ConjugacyClassSubgroups(G,Q);
    QH:=ConjugacyClassSubgroups(H,Q);
    elQG:=Elements(QG);
    fs:=Filtered(elQG,a->not RepresentativeAction(G,Q,a) in H);
    xG:=Set(fs,i->AsSubgroup(G,Intersection(Q,i)));
    yH:=Set(fs,i->AsSubgroup(H,Intersection(H,i)));
    pccsubG:=ModularConjugacyClassesSubgroups(G,p);
    pccsubH:=ModularConjugacyClassesSubgroups(H,p);

    zG:=Filtered(pccsubG,i->not(GroupSetsContaining(G,Elements(i),xG)));
    zH:=Filtered(pccsubH,i->not(GroupSetsContaining(H,Elements(i),yH)));
    return rec(x:=xG,y:=yH,z_conjGlobal:=zG,z_conjLocal:=zH);
end);