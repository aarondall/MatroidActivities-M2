-- -*- coding: utf-8 -*-
--  MatroidActivities.m2
--
--  Copyright (C) 2016 Aaron Dall <aaronmdall@gmail.com>
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  This program is free software; you can redistribute it
--  and/or modify  it under the terms of the GNU General
--	Public License as	published by  the Free Software Found-
-- 	ation; either version 2 of the License, or (at  your
--  option) any later version.
--
--	This program is distributed in the hope that it will be
--	useful, but  WITHOUT ANY WARRANTY; without even the
--	implied warranty of  MERCHANTABILITY or FITNESS FOR A
--	PARTICULAR PURPOSE.  See the GNU  General Public License
--	for more details.
--
--  You should have received a copy of the GNU General
--	Public License along with this program; if not, write
--	to the Free Software Foundation, Inc.,  59 Temple Place,
--	Suite 330, Boston, MA 02111-1307 USA.
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
newPackage (
	"MatroidActivities",
	Version => "0.1",
	Date => "2016 07 24",
	Authors => {{Name => "Aaron Dall", Email => "aaronmdall -at- gmail.com", HomePage => "http://aarondall.com"}},
	PackageExports => {"Posets","Matroids"},
	Headline => "MatroidActivities",
	DebuggingMode => true
	)

needsPackage"SimpleDoc"

export {
	--Official functions--
	--"relativeOrder",				 -- internal function
	--"stringToList",				 -- internal function
	--"listToString",				 -- internal function
	"orderedMatroid",				 -- documented
	"orderedGround",				 -- documented
	"orderedBases",					 -- documented
	"orderedCircuits",				 -- documented
	"orderedCocircuits",			 -- documented
	"orderedFlats",					 -- documented
	"activeElements",				 -- documented
	"duallyActiveElements",			 -- documented
	"externallyActiveElements",		 -- documented
	"externallyPassiveElements",	 -- documented
	"internallyActiveElements",		 -- documented
	"internallyPassiveElements",	 -- documented
	"externalOrder",				 -- documented
	"internalOrder",				 -- documented
	"minimalBasis",					 -- documented
	"internalBasisDecomposition",	 -- documented
	"basisType",					 -- documented
	"bjornersPartition",			 -- documented
	"parallelClasses",				 -- documented
	"matroidHVector",				 -- documented
	"texActiveOrder",				 -- documented

	--Tests--
	"isActive",						 -- documented
	"isDuallyActive",				 -- documented
	"isInternallyPerfect",			 -- documented

	--Types--
	"OrderedMatroid" --hashTable 	 -- documented
	}

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

--  INTERNAL METHODS --

--  Internal method that converts a set A to a list ordered
--  with respect to the list L
relativeOrder = method()
relativeOrder (Set, List) := (A,L) -> (
	B := select(L, l -> member(l,A));
	C := select(toList A, a -> not member(a,L));
	join(B,C))

-- Internal methods for converting between strings and lists.
-- Used to beautify tex output of posets
stringToList = S -> flatten apply(characters S, s -> apply(characters s, e-> value e))
listToString = L -> concatenate apply(L, l -> toString l)



-- ORDERED MATROID FUNCTIONALITY --

--  Setting up the OrderedMatroid Type
OrderedMatroid = new Type of HashTable

globalAssignment OrderedMatroid
net OrderedMatroid := X -> (
	if hasAttribute(X, ReverseDictionary) then toString getAttribute(X, ReverseDictionary)
	else "OrderedMatroid"
)

OrderedMatroid == OrderedMatroid := (M, N) ->  (
	isomorphic (M.matroid, N.matroid) and
	all(M.orderedGround, N.orderedGround, (i,j) -> rk_(M.matroid) {i,j}==1)
	)

--	Make an ordered matroid from an ordered subset of the
--	ground set by declaring the that elements of the subset
--	the elements of the subset come first (in the order
--	given) and the remaining elements come last, ordered
-- 	by the natural order on the ground set.

orderedMatroid = method(TypicalValue => HashTable)
orderedMatroid (Matroid, List) := (M,L) -> (
	r := rk M;
	E := relativeOrder(M.ground, L);
	n := #E;
	B := for b in M.bases list relativeOrder(b,E);
	orderedB := select(subsets (E,r), l -> member(set l,M.bases));
	orderedCi := apply(circuits M, c -> relativeOrder(c, E));
	orderedCoci := apply(circuits dualMatroid M, c -> relativeOrder(c, E));
	OM := new OrderedMatroid from {
		symbol matroid => M,
		symbol orderedGround => E,
		symbol orderedBases => orderedB,
		symbol orderedCircuits => orderedCi,
		symbol orderedCocircuits => orderedCoci
	};
	OM
)
orderedMatroid (Matroid) := M -> (orderedMatroid(M,{}))
orderedMatroid (Matrix, List) := (M,L) -> orderedMatroid (matroid M, L)
orderedMatroid (Graph, List) := (G,L) -> orderedMatroid (matroid G, L)

-- Ordered analogues of matroidal objects
orderedFlats = method()
orderedFlats OrderedMatroid := M -> (
	apply(flats M.matroid, L -> apply(L, f->  relativeOrder(f, M.orderedGround)))
		)
orderedFlats Matroid := M -> (
	orderedFlats orderedMatroid M)

--  Test if an element of an ordered matroid is active with respect to a set --
isActive = method(TypicalValue => Boolean)
isActive (OrderedMatroid, List, ZZ) := (M, A, e) -> (
 	any(M.orderedCircuits, c -> e == first c and isSubset(c, append(A,e))))
isActive (Matroid, List, ZZ) := (M, A, e) -> (
	isActive (orderedMatroid M,A,e))

--  Test if an element of an ordered matroid is active in the dual matroid with respect to a set --
isDuallyActive = method(TypicalValue => Boolean)
isDuallyActive (OrderedMatroid, List, ZZ) := (M, A, e) -> (
 	any(M.orderedCocircuits, c -> e == first c and isSubset(c, append(select(M.orderedGround, f -> not member(f,A)),e))))
isDuallyActive (Matroid, List, ZZ) := (M, A, e) -> (
	isDuallyActive (orderedMatroid M,A,e))

activeElements = method(TypicalValue=>List)
activeElements (OrderedMatroid, List) := List => (M, A) -> (
	if not isSubset(A, M.orderedGround)
		then error "expected a subset of the ground set"
	else
		select(M.orderedGround, e -> isActive(M, A, e)))
activeElements (Matroid, List) := List => (M, A) -> (
	activeElements(orderedMatroid M, A))

duallyActiveElements = method(TypicalValue=>List)
duallyActiveElements (OrderedMatroid, List) := List => (M, A) -> (
	if not isSubset(A, M.orderedGround)
		then error "expected a subset of the ground set"
	else
		select(M.orderedGround, e -> isDuallyActive(M, A, e)))
duallyActiveElements (Matroid, List) := List => (M, A) -> (
	activeElements(orderedMatroid M, A))

externallyActiveElements = method(TypicalValue => List)
externallyActiveElements (OrderedMatroid, List) := List => (M,A) ->(
	relativeOrder (set activeElements(M,A) - set A, M.orderedGround))
externallyActiveElements (Matroid, List) := List => (M,A) ->(
	externallyActiveElements(orderedMatroid M, A))

externallyPassiveElements = method(TypicalValue => List)
externallyPassiveElements (OrderedMatroid, List) := List => (M,A) -> (
	relativeOrder ((set M.orderedGround - set activeElements(M,A)) - set A, M.orderedGround))
externallyPassiveElements (Matroid, List) := List => (M,A) ->(
	externallyPassiveElements (orderedMatroid M, A))

internallyActiveElements = method(TypicalValue => List)
internallyActiveElements (OrderedMatroid, List) := List => (M,A) -> (
	relativeOrder (set A * set duallyActiveElements(M,A), M.orderedGround)
	)
internallyActiveElements (Matroid, List) :=  (M,A) -> (
	internallyActiveElements(orderedMatroid M, A))


internallyPassiveElements = method(TypicalValue => List)
internallyPassiveElements (OrderedMatroid, List) := List =>  (M,A) ->(
	relativeOrder (set A - set internallyActiveElements(M,A),M.orderedGround))
internallyPassiveElements (Matroid, List) := List =>  (M,A) ->(
	internallyPassiveElements (orderedMatroid M, A))

externalOrder = method(TypicalValue => Poset)
externalOrder (OrderedMatroid) := Poset => M -> (
	h := hashTable apply(M.orderedBases, b -> b => externallyActiveElements(M,b));
	cmp := (a,b) -> isSubset(stringToList a, join(stringToList b,h#(stringToList b)));
	poset (apply(M.orderedBases, b -> listToString b),cmp))
externalOrder (Matroid) := Poset => M ->(
	externalOrder orderedMatroid M)

internalOrder = method(TypicalValue => Poset)
internalOrder (OrderedMatroid) := Poset => M -> (
	h := hashTable apply(M.orderedBases, b -> b => internallyPassiveElements(M,b));
	cmp := (a,b) -> isSubset(h#(stringToList a), h#(stringToList b));
	poset (apply(M.orderedBases, b -> listToString b),cmp))
internalOrder (Matroid) := Poset => (M) -> (
	internalOrder orderedMatroid M)
internalOrder (Matrix) := Poset => (M) -> (
	internalOrder orderedMatroid matroid M)


--compute a minimal basis from an independent set
--will give undesired results for dependent sets
minimalBasis = method(TypicalValue => List)
minimalBasis (OrderedMatroid, List) := List => (M, I) -> (
	p := (position(M.orderedBases, b -> isSubset(I, b)));
	if class p === ZZ then (M.orderedBases)#p else error "expected an independent set")
minimalBasis (Matroid, List) := List => (M, I) -> (
	minimalBasis(orderedMatroid M, I))

internalBasisDecomposition = method(TypicalValue => List)
internalBasisDecomposition (OrderedMatroid, List) := List => (M, b) ->(
	B0 := first M.orderedBases;
	IA := internallyActiveElements (M, b);
	IP := internallyPassiveElements (M, b);
	S := toList (set IP - set B0);
	T := toList (set IP - S);
	{S,T,IA})
internalBasisDecomposition (Matroid, List) := List => (M, L) ->(
	internalBasisDecomposition (orderedMatroid M,L))


basisType = method()
basisType (OrderedMatroid,List) := (M,b) -> (
	(S,T,A):= toSequence internalBasisDecomposition(M,b);
	projections := flatten for s in S list (
		newBs := minimalBasis(M, join({s},T));
		(internalBasisDecomposition(M,newBs))#1);
	if projections == T
		then "perfect"
	else if unique projections == T
		then "abundant"
	else "deficient"
	)
basisType (Matroid, List) := (M,b) -> (
	basisType (orderedMatroid M, b))

isInternallyPerfect = method(TypicalValue => Boolean)
isInternallyPerfect (OrderedMatroid) := Boolean => (M) -> (
	topElements := for b in maximalElements internalOrder M list (
		flatten stringToList b);
	check := b -> basisType(M,b) == "perfect";
	all(topElements, check)
	)
-- Test if any permutation makes a matroid into an internally perfect matroid
isInternallyPerfect Matroid := Boolean => M -> (
	checkPermsOfBasis := b -> (
		P := permutations toList b;
		k := position(P, p-> isInternallyPerfect orderedMatroid (M, p));
		if class k === ZZ then P#k else null
		);
	j := (position(M.bases, b -> checkPermsOfBasis b =!= null));
	j === ZZ
	)

bjornersPartition = method(TypicalValue => List)
bjornersPartition OrderedMatroid := List => M -> (
	n := #M.orderedGround;
	B := booleanLattice n;
	--convert
	labels := apply(B.GroundSet, s ->
	 s => M.orderedGround_(select(toList(0..<n), i -> s#i == toString 1))
		);
	labeledB:=labelPoset(B, new HashTable from labels);
	apply(M.orderedBases, b -> (
		bInterval := closedInterval (
			labeledB,
			internallyPassiveElements(M,b),
			relativeOrder(set join(b, externallyActiveElements (M,b)), M.orderedGround));
		[flatten minimalElements bInterval, flatten  maximalElements bInterval]))
	)
bjornersPartition Matroid := List => M -> (
	bjornersPartition orderedMatroid M)

--  ADDITIONAL UNORDERED MATROID FUNCTIONALITY --

parallelClasses = method(TypicalValue => List)
parallelClasses Matroid := M -> (
	select(flatten flats M, f -> rk_M f == 1))
parallelClasses OrderedMatroid := OM -> parallelClasses (OM.matroid)

matroidHVector = method(TypicalValue => List)
matroidHVector Matroid := M -> (
	t := tuttePolynomial M;
    L := flatten entries (coefficients sub(t, (gens ring t)#1 => 1))#1;
    Z := toList(rk M -#L + 1 : 0); --trailing zeros
    h := for l in L list sub(l,ZZ);
	join (h,Z)
    )

-- TEX ACTIVE ORDERS
texActiveOrder = method(Options => {symbol Jitter => false})
texActiveOrder Poset := String => opts -> P -> print (
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    -- edge list to be read into TikZ
    if not P.cache.?coveringRelations then coveringRelations P;
    edgelist := apply(P.cache.coveringRelations, r -> concatenate(toString first r, "/", toString last r));
    -- Find each level of P and set up the positioning of the vertices.
    if not P.cache.?filtration then filtration P;
    F := P.cache.filtration;
    levelsets := apply(F, v -> #v-1);
    scalew := min{1.5, 15 / (1 + max levelsets)};
    scaleh := min{2 / scalew, 15 / #levelsets};
    halflevelsets := apply(levelsets, lvl -> scalew * lvl / 2);
    spacings := apply(levelsets, lvl -> scalew * toList(0..lvl));
    -- The TeX String
    "\n\\tikzstyle{every node} = [draw = black, thick, fill = white, rectangle, inner sep = 2pt]\n\\begin{tikzpicture}[scale = 1]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list
            {"    \\node ",
            " (",toString F_i_j,") at (-",toString halflevelsets_i,"+", toString ((if opts.Jitter then random(scalew*0.2) else 0) + spacings_i_j),",",toString (scaleh*i),")",
            ("  {"| tex toString (value P.GroundSet_(F_i_j) + value concatenate apply(apply(flatten apply(characters P.GroundSet_(F_i_j), i -> apply(characters i, j-> value j)), l -> "1"), l -> toString l)) | "};\n")}
            ) |

    concatenate("  \\foreach \\to/\\from in ", toString edgelist, "\n\\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )
-- Caveat: Use tex Poset if you want to suppress labels
-- Caveat: This might work for any poset whose ground set is a list of strings. Use with caution.
------------------------
-- End of source code --
------------------------
-------------------------
-- Begin documentation --
-------------------------
beginDocumentation()
doc ///
	Key
		MatroidActivities
	Headline
		a package for computations with ordered matroids
	Description
		Text
			@EM "MatroidActivities"@ is an extension of the
			@TO Matroids@ package that facilitates computation of the general
			matroid activities defined by Las Vergnas in [LV01].
			In order to make these computations we introduce the new type
			@TO OrderedMatroid@ consisting of a matroid together with a linear
			order on the ground set of the matroid.
			In addition to methods for computing internal and external
			activities of arbitrary subsets of the ground set of an ordered
			matroid, there are also methods for computing the internal and
			external orders of an ordered matroid as well as the Bjorner
			partition of the boolean lattice (see [Bj92]) induced by a given
			linear ordering of the ground set. @BR{}@ @BR{}@

			{\bf Setup}

			This package uses the package @TO Matroids@, so install this first.
			The source code can be found @HREF{ "https://github.com/jchen419/Matroids-M2", "here"}@.

			Place the source file @TT "MatroidActivities.m2"@ somewhere into
			the M2 search path (type path to see it) and install the package
			by calling @TO installPackage@ on "MatroidActivities".

			{\bf References}@BR{}@
			@UL{
				"[LV01] Active Orders for Matroid Bases  (M. Las Vergnas,
				2001)",
				"[Bj92] Homology and shellability of matroids and geometric
				lattices, (A. Bjorner, 2001)"
			}@
	SeeAlso
		Matroids
		matroid
///

doc ///
    Key
        parallelClasses
    	(parallelClasses, OrderedMatroid)
    	(parallelClasses, Matroid)
    Headline
    	compute the parallel classes of a matroid
    Usage
    	P = parallelClasses OM
    	P = parallelClasses M
    Inputs
    	OM:OrderedMatroid
    	M:Matroid
    Outputs
    	:List
    Description
        Text
        	Computes the parallel classes of a matroid or an ordered matroid, that is, the @TO flats@ of rank one.


        Example
        	m := sub(matrix {{1,0,1,1},{0,1,1,0}},QQ)
        	M = matroid m;
        	parallelClasses M
    SeeAlso
    	(symbol ==, OrderedMatroid, OrderedMatroid)
///

doc ///
	Key
		OrderedMatroid
	Headline
		the class of ordered matroids
	Description
		Text
			An ordered matroid is a matroid together with a linear order on
			its ground set. In this package an ordered matroid is stored as
			a hash table consisting of a @TO matroid@ and two lists: @TO2 {orderedGround, "ordered ground"}@ and @TO2 {orderedBases, "ordered bases"}@. The list
			 orderedGround induces the linear order on the ground set
			  given by $e_i < e_j$ if $i$ precedes $j$ in the list.
			  The list orderedBases is the lex-ordering (with respect to orderedGround) of the bases of M, each ordered with respect to orderedGround.
		Example
			M = matroid completeGraph 4;
			OM = orderedMatroid (M,{1,3,5,2,4,0})
			truncateOutput 70; --used to limit the size of the output
			peek OM
			OM.matroid == matroid completeGraph 4
			OM.orderedBases
			OM.orderedGround

	Caveat
			The method @TO matroid@ does not check that the result is
			in fact a matroid and @TO2 {orderedMatroid, "ordered matroid"}@ inherits this
			property. To check that the ordered bases of an ordered
			matroid satisfy the basis exchange axiom we use @TO isValid@ on
			the key "matroid".

	SeeAlso
		orderedMatroid

///

doc ///
    Key
        (symbol ==, OrderedMatroid, OrderedMatroid)
    Usage
    	OM1 == OM2
    Inputs
    	OM1:OrderedMatroid
    	OM2:OrderedMatroid
    Outputs
    	:Boolean
    Description
        Text
        	Two @TO2{orderedMatroid, "ordered matroids"}@ are declared to be equal if their underlying unordered matroids are @TO isomorphic@ and if their @TO2 {orderedGround, "ordered ground"}@ sets differ by a permutation that acts only on @TO2 {parallelClasses, "parallel classes"}@ of the underlying matroid.

        Example
        	m := sub(matrix {{1,0,1,1},{0,1,1,0}},QQ);
        	M = orderedMatroid (m,{});
        	M1 = orderedMatroid (m,{3,1,2,0});
        	M == M1
        	M2 = orderedMatroid (m,{1,3,2,0});
        	M == M2
///

doc ///
	Key
		orderedGround
	Headline
		the ordered ground set of an ordered matroid
	Usage
		M.orderedGround
	Inputs
		M:OrderedMatroid
	Outputs
		L:List
	Description
		Text
			The ordered ground set of M is stored as a value in the hash table.

		Example
			M = orderedMatroid (completeGraph 4, {0,3,1,4,2,5});
			truncateOutput 70;
			peek M
			M.orderedGround

	SeeAlso
		orderedBases
		orderedCircuits
		orderedCocircuits
///

doc ///
	Key
		orderedBases
	Headline
		the ordered bases of an ordered matroid
	Usage
		M.orderedBases
	Inputs
		M:OrderedMatroid
	Outputs
		L:List
	Description
		Text
			Each element of this list is a basis of the underlying unordered matroid M.@TO matroid@ ordered with respect to the @TO2 {orderedGround, "ordered ground"}@ set of M. Moreover, the whole list is ordered by the lexicographical order induced by the @TO2 {orderedGround, "ordering"}@ on the ground set.

		Example
			M = orderedMatroid (completeGraph 4, {0,3,1,4,2,5});
			M.orderedBases

	SeeAlso
		orderedCircuits
		orderedCocircuits
		orderedGround
		orderedMatroid
		OrderedMatroid
///

doc ///
	Key
		orderedCircuits
	Headline
		the ordered circuits of an ordered matroid
	Usage
		M.orderedCircuits
	Inputs
		M:OrderedMatroid
	Outputs
		C:List
			consisting of the ordered circuits
	Description
		Text
			Each element of @TO2 {orderedCircuits, "ordered circuits"}@ is a circuit of the underlying unordered matroid that is ordered with respect to @TO2 {orderedGround, "ordered ground"}@, the linear ordering on the ground set of M. Unlike for @TO2 {orderedBases, "ordered bases"}@, we do not sort the list of ordered circuits with respect to the @TO2 {orderedGround, "ordered ground"}@.

		Example
			M = orderedMatroid (completeGraph 4, {0,3,1,4,2,5});
			M.orderedCircuits

	SeeAlso
		orderedBases
		orderedCocircuits
		orderedGround
		orderedMatroid
		OrderedMatroid
///

doc ///
	Key
		orderedCocircuits
	Headline
		the ordered cocircuits of an ordered matroid
	Usage
		M.orderedCocircuits
	Inputs
		M:OrderedMatroid
	Outputs
		C:List
			consisting of the ordered cocircuits
	Description
		Text
			Each element of @TO orderedCocircuits, "ordered cocircuits"@ is a circuit of the dual of the underlying unordered matroid that is ordered with respect to @TO2 {orderedGround, "ordered ground"}@, the linear ordering on the ground set of M. Unlike for @TO2 {orderedBases, "ordered bases"}@, we do not sort the list of ordered cocircuits with respect to the @TO2 {orderedGround, "ordered ground"}@.

		Example
			M = orderedMatroid (completeGraph 4, {0,3,1,4,2,5});
			M.orderedCocircuits

	SeeAlso
		orderedBases
		orderedCircuits
		orderedGround
		orderedMatroid
		OrderedMatroid
///

doc ///
	Key
		orderedMatroid
		(orderedMatroid, Matroid, List)
		(orderedMatroid, Matroid)
		(orderedMatroid, Matrix, List)
		(orderedMatroid, Graph, List)
	Headline
		construct an ordered matroid
	Usage
		OM = orderedMatroid(M, L)
		OM = orderedMatroid(M)
		OM = orderedMatroid(N, L)
		OM = orderedMatroid(G, L)
	Inputs
		M:Matroid
		L:List
			consisting of some ground set elements
		N:Matrix
		G:Graph
	Outputs
		OM:HashTable
			consisting of the matroid and the order induced by the list
	Description
		Text
			First we construct an ordered matroid from a @TO Matroid@ object M and a list L. The list L orders the (indices of the) ground set E of M as follows:@BR{}@
			@BR{}@
				(1) the elements of E that appear in L appear first and in the same order as they appear in L; @BR{}@
				(2) the elements of E not in L appear after all that do and are ordered with respect to the natural ordering on E.@BR{}@
				@BR{}@
			In particular L need not be a permutation of E, nor even a subset.
			The next examples illustrate these ideas by giving three lists that yield the same orderedMatroid.

		Example
			M = matroid completeGraph 4
			L1 = {4,3,2,0,1,5}; -- a permutation on the ground set
			OM1 = orderedMatroid(M, L1);
			OM1.orderedGround
			L2 = {4,3,2}; -- a sublist of L1
			OM2 = orderedMatroid(M, L2);
			OM2 == OM1
			L3 = {4,18,-1,3,1/2,2};
			OM3 = orderedMatroid(M, L3);
			OM3.orderedGround


		Text
			It is often desirous to view a given matroid as an ordered matroid with the natural ordering on the ground set.
			In this case one can omit the list from the input data.

		Example
			orderedMatroid M == orderedMatroid (M,{})

		Text
			One can convert a matrix or a graph into an ordered matroid with the natural ordering on the ground set as follows.

		Example
			M = matrix {{1, 1, 1, 0, 0, 0}, {-1, 0, 0, 1, 1, 0}, {0, -1, 0, -1, 0, 1}}
			OM1 = orderedMatroid (M,{3,0,4,1,5,2});
			OM2 = orderedMatroid (completeGraph 4, {3,0,4,1,5,2});
			OM1 == OM2

		Text

		Example
				M = matroid completeGraph 4;
				OM1 = orderedMatroid M;
				OM2 = orderedMatroid (M, {})

	SeeAlso
		matrix
		graph
		(symbol ==, OrderedMatroid, OrderedMatroid)
		orderedBases
		orderedCircuits
		orderedCocircuits
		orderedGround
		orderedMatroid
		OrderedMatroid
///

doc ///
	Key
		orderedFlats
		(orderedFlats, OrderedMatroid)
		(orderedFlats, Matroid)
	Headline
		the ordered flats of an ordered matroid
	Usage
		C = orderedFlats(OM)
		C = orderedFlats(M)
	Inputs
		OM:OrderedMatroid
		M:Matroid
	Outputs
		F:List
			consisting of the ordered flats
	Description
		Text
			Applying this method to an ordered matroid returns the flats of the underlying matroid as lists that are ordered with respect to the given linear ordering on the ground set.

			For an unordered matroid, the linear order is assumed to be the natural order on the ground set.

		Example
			F1 = orderedFlats orderedMatroid (matroid completeGraph 4, {5,2,4,1,0})
			F2 = orderedFlats matroid completeGraph 4

	SeeAlso
		OrderedMatroid
		orderedMatroid
		orderedCircuits
		orderedBases
///

doc ///
	Key
		isActive
		(isActive, OrderedMatroid, List, ZZ)
		(isActive, Matroid, List, ZZ)
	Headline
		test if an element is active
	Usage
		isActive(OM,A,e)
		isActive(M,A,e)
	Inputs
		OM:OrderedMatroid
			an ordered matroid
		M:Matroid
			a matroid
		A:List
			a list of indices of ground set elements
		e:ZZ
			an element of the ground set
	Outputs
		:Boolean
			whether e is active in OM with respect to A
	Description
		Text
			An element $e$ of the ground set of an ordered matroid $OM$ is
			active with respect to a subset $A$ of the ground set if there is
			an ordered circuit $C$ of $OM$ such that $C \subseteq A \cup
			\{e\}$ and $e$ is the smallest element of $C$ with respect to the
			linear order on the ground set.

			For an unordered matroid, @TO isActive@ tests activity with respect to the natural ordering on the ground set.

			The next example shows that the property of being active depends on the given order of the ground set.

		Example
			M = matroid completeGraph 3
			OM1 = orderedMatroid (M,{0,1,2});
			isActive(OM1, {1,2},0)
			OM2 = orderedMatroid(M,{2,0,1}); -- changing the order
			isActive(OM2, {1,2},0) -- effects activity
	Caveat
		Most of the routines in this package use @TO isActive@ or @TO isDuallyActive@ as a subroutine, and therefore depend on the given linear order @TO2 {orderedGround, "ordered ground"}@.
	SeeAlso
		orderedMatroid
		orderedGround
		isDuallyActive
		externallyActiveElements
		externallyPassiveElements
		internallyActiveElements
		internallyPassiveElements
///

doc ///
	Key
		isDuallyActive
		(isDuallyActive, OrderedMatroid, List, ZZ)
		(isDuallyActive, Matroid, List, ZZ)
	Headline
		test if an element is active in the dual
	Usage
		isDuallyActive(OM,A,e)
		isDuallyActive(M,A,e)
	Inputs
		OM:OrderedMatroid
			an ordered matroid
		M:Matroid
			a matroid
		A:List
			a list of indices of ground set elements
		e:ZZ
			an element of the ground set
	Outputs
		:Boolean
			whether e is active in the ordered dual of OM with respect to A
	Description
		Text
			An element $e$ of the ground set of an ordered matroid $OM$ is
			active in the dual of $OM$ with respect to a subset $A$ of the ground set if there is
			an ordered cocircuit $C^*$ of $OM$ such that $C^* \subseteq A \cup
			\{e\}$ and $e$ is the smallest element of $C^*$ with respect to the
			linear order on the ground set, @TO2 {orderedGround, "ordered ground"}@.

			For an unordered matroid, @TO isDuallyActive@ tests activity in the ordered @TO2{dualMatroid,"dual"}@ with respect to the natural ordering on the ground set.

			The next example shows that the property of being dually active depends on the given order of the ground set.

		Example
			M = matroid completeGraph 3;
			OM1 = orderedMatroid (M,{0,1,2});
			isDuallyActive(OM1, {0,1},0)
			OM2 = orderedMatroid(M,{2,1,0})
			isDuallyActive(OM2, {0,1},0)
	Caveat
		Most of the routines in this package use @TO isActive@ or @TO isDuallyActive@ as a subroutine, and therefore depend on the given linear order @TO2 {orderedGround, "ordered ground"}@.
	SeeAlso
		orderedMatroid
		orderedGround
		isActive
		externallyActiveElements
		externallyPassiveElements
		internallyActiveElements
		internallyPassiveElements
///

doc ///
	Key
		activeElements
		(activeElements, OrderedMatroid, List)
		(activeElements, Matroid, List)
	Headline
		the active elements with respect to a subset
	Usage
		Act = activeElements(OM,A)
		Act = activeElements(M,A)
	Inputs
		OM:OrderedMatroid
		M:Matroid
		A:List
			of indices of ground set elements
	Outputs
		Act:List
			consisting of the active elements of the ground set of an ordered matroid with respect to the elements of A
	Description
		Text
			For an ordered matroid the active elements with respect to the elements in A are computed with respect to the given linear order of the ground set and returned as a list ordered with respect to @TO2 {orderedGround, "ordered ground"}@.

			For a matroid, the natural order on the ground set is taken as the linear order.

		Example
			M = matroid completeGraph 3
			OM = orderedMatroid(M,{2,0,1})
			Act = activeElements(OM, {0,1})

		Text
			In general, varying the order varies the active elements.

		Example
			OM1 = orderedMatroid M
			Act1 = activeElements(M, {0,1})
///

doc ///
	Key
		duallyActiveElements
		(duallyActiveElements, OrderedMatroid, List)
		(duallyActiveElements, Matroid, List)
	Headline
		the active elements with respect to a subset
	Usage
		Act = duallyActiveElements(OM,A)
		Act = duallyActiveElements(M,A)
	Inputs
		OM:OrderedMatroid
		M:Matroid
		A:List
			of indices of ground set elements
	Outputs
		Act:List
			consisting of the active elements of the ground set of the dual of an ordered matroid with respect to the elements of A
	Description
		Text
			For an ordered matroid the active elements of the dual with respect to the set A are computed with respect to the given linear order of the ground set and returned as a list ordered with respect to @TO2 {orderedGround, "ordered ground"}@.

			For a matroid, the natural order on the ground set is taken as the linear order.

		Example
			M = matroid completeGraph 3;
			OM = orderedMatroid(M,{2,0,1});
			Act = duallyActiveElements(OM, {0,1})

		Text
			As with @TO activeElements@, changing the order on the ground set can change the dually active elements of a set.

		Example
			OM1 = orderedMatroid (M,{0,1,2});
			Act1 = duallyActiveElements(OM1, {0,1})
///

doc ///
	Key
		externallyActiveElements
		(externallyActiveElements, OrderedMatroid, List)
		(externallyActiveElements, Matroid, List)
	Headline
		the externally active elements of a subset of the ground set
	Usage
		EA = externallyActiveElements(OM,A)
		EA = externallyActiveElements(M,A)
	Inputs
		OM:OrderedMatroid
		M:Matroid
		A:List
			consisting of indices of ground set elements
	Outputs
		EA:List
			consisting of the externally active elements of OM with respect to A
	Description
		Text
			Given an ordered matroid and a subset A of the ground set, an element e of the ground set is externally active with respect to A if e is active with respect to A and e is not an element of A.

			For the cycle matroid M of the complete graph on three vertices with the natural order, we see that then there are no externally active elements with respect to the set consisting of 0 and 1.

		Example
			M = matroid completeGraph 3;
			EA = externallyActiveElements(M, {0,1})

		Text
			On the other hand, if the linear order on M is given by 2 < 0 < 1, then e = 2 is the only externally active element.

		Example
			OM = orderedMatroid(M,{2,0,1})
			EA = externallyActiveElements(OM, {0,1})
	SeeAlso
		isActive
		orderedMatroid
///

doc ///
	Key
		externallyPassiveElements
		(externallyPassiveElements, OrderedMatroid, List)
		(externallyPassiveElements, Matroid, List)
	Headline
		the externally passive elements of a set
	Usage
		EP = externallyPassiveElements(OM,A)
		EP = externallyPassiveElements(M,A)
	Inputs
		OM:OrderedMatroid
		M:Matroid
		A:List
			consisting of indices of ground set elements
	Outputs
		EA:List
			consisting of the externally passive elements of an ordered matroid with respect to A
	Description
		Text
			Given an ordered matroid, an element e of the ground set is externally passive with respect to the set A if it is not in A and it is not externally active with respect to A.

			For the cycle matroid M of the complete graph on three vertices with the natural order, we see that e = 2 is externally passive with respect to the set consisting of 0 and 1.

		Example
			M = matroid completeGraph 3
			EP = externallyPassiveElements(M, {0,1})

		Text
			On the other hand, if the linear order on M is given by 2 < 0 < 1 then there are no externally passive elements.

		Example
			OM = orderedMatroid(M,{2})
			EP = externallyPassiveElements(OM, {0,1})

	SeeAlso
		orderedMatroid
		isActive
		externallyActiveElements
///

doc ///
	Key
		internallyActiveElements
		(internallyActiveElements, OrderedMatroid, List)
		(internallyActiveElements, Matroid, List)
	Headline
		the internally active elements of a set
	Usage
		IA = internallyActiveElements(OM,A)
		IA = internallyActiveElements(M,A)
	Inputs
		OM:OrderedMatroid
		M:Matroid
		A:List
			consisting of elements of the ground set
	Outputs
		IA:List
			consisting of internally active elements of A
	Description
		Text
			For an ordered matroid $OM$ with $L$ the linear order on the ground set, an element $e$ of $E$ is internally active with respect to a subset $A \subseteq E$ if $e \in A$ and there is an ordered cocircuit $C^*$ of $OM$ such that (1) $C^* \subseteq E-A \cup \{e\}$ and (2) $e$ is the least element of $C^*$ with respect to $L$.

			Internal activity depends on the order of the ground set.

		Example
			M = matroid completeGraph 3
			IA1 = internallyActiveElements(M, {0,1})
			OM = orderedMatroid(M,{2})
			IA2 = internallyActiveElements(OM, {0,1})

		Text
			By matroid duality we have that an element $e$ is internally active with respect to $A$ if and only if  $e$ is externally passive with respect to $E-A$.

		Example
			EP1 = externallyPassiveElements(M, {2});
			EP1 == IA1
	SeeAlso
		isActive
		orderedMatroid
		externallyPassiveElements
///

doc ///
	Key
		internallyPassiveElements
		(internallyPassiveElements, OrderedMatroid, List)
		(internallyPassiveElements, Matroid, List)
	Headline
		the internally passive elements of a set
	Usage
		IA = internallyPassiveElements(OM,A)
		IA = internallyPassiveElements(M,A)
	Inputs
		OM:OrderedMatroid
		M:Matroid
		A:List
			consisting of elements of E
	Outputs
		IA:List
			consisting of internally passive elements of A
	Description
		Text
			Given an ordered matroid, an element e of the ground set is internally passive with respect to the set A if e is not internally active with respect to A.

		Example
			M = matroid completeGraph 3
			OM = orderedMatroid(M,{2,0,1})
			IA1 = internallyPassiveElements(OM, {0,1})

		Text
			Internal passivity depends on the order of the ground set.

		Example
			IA2 = internallyPassiveElements(M, {0,1})
	SeeAlso
		isActive
		internallyActiveElements
		orderedMatroid
///

doc ///
	Key
		externalOrder
		(externalOrder, OrderedMatroid)
		(externalOrder, Matroid)
	Headline
		the external order of an ordered matroid
	Usage
		P = externalOrder(OM)
		P = externalOrder(M)
	Inputs
		OM:OrderedMatroid
			an ordered matroid with linear order on the ground set E
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
	Outputs
		P:Poset
			the external order of an ordered matroid
	Description
		Text
			The external order of an ordered matroid OM is the poset
			on the @TO2{orderedBases},"ordered bases"@ of defined by the relation b1 < b2 if b1 is a subset of the union of b2 and the @TO2{externallyActiveElements,"externally active elements"}@ of b2.
			(See [LV01] for equivalent conditions.)

		Example
			M = matroid completeGraph 3
			P = externalOrder(M)

		Text
			For some simple examples the external order is an invariant of the underlying unordered matroid, that is, it is independent of the linear order on the ground set.
			Let us illustrate this with the three cycle.

		Example
			isomorphismClasses = removeIsomorphicPosets (
				for p in permutations 3 list (
					externalOrder orderedMatroid (M,p)))

		Text
			In general, however, the isomorphism class of the external order can vary with the given linear order.
			We illustrate this for the cycle matroid of the graph obtained from the complete graph $K_4$ by removing one edge.

		Example
			M = matroid sub(matrix {{1, 0, 1, 1, 0}, {-1, 1, 0, 0, 0}, {0, 0, -1, 0, 1}}, QQ);
			P = externalOrder(M);
			isomorphismClasses = tally removeIsomorphicPosets (
				for p in permutations 5 list (
					externalOrder orderedMatroid (M,p)))

		Text
			In [LV01], it is shown that the external order is a graded poset and that it becomes a graded lattice once an artificial bottom element is added.

		Example
			isGraded P
			isLattice (adjoinMin P)

		Text
			Though the external order of an ordered matroid is not an
			invariant of the underlying matroid, its rank generating function
			is.
			More precisely, for any linear ordering of the ground set of an
			unordered matroid $M$, the rank generating function of the poset
			dual of the  induced external order is the matroid $h$-polynomial
			of the dual unordered matroid.

		Example
			R = ZZ[x,y,q];
			p = sub(tuttePolynomial M,R);
			h = q^2*sub(p, {x => 1, y => 1/q}); -- the h-polynomial of the dual
			RGF = sub(rankGeneratingFunction dual externalOrder M,R);
			RGF == h

		Text
			@BR{}@ @BR{}@
			{\bf References}@BR{}@
			@UL{
				"[LV01] Active Orders for Matroid Bases  (M. Las Vergnas,
				2001)",
				}@
///

doc ///
	Key
		internalOrder
		(internalOrder, OrderedMatroid)
		(internalOrder, Matroid)
		(internalOrder, Matrix)
	Headline
		the internal order of an ordered matroid
	Usage
		P = internalOrder(OM)
		P = internalOrder(M)
		P = internalOrder(m)
	Inputs
		OM:OrderedMatroid
			an ordered matroid with linear order on the ground set E
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
		m:Matrix
	Outputs
		P:Poset
			the internal order of an ordered matroid
	Description
		Text
			For an ordered matroid OM, the partially ordered set on the basis of OM
			where b1 < b2 if every @TO2{internallyPassiveElements, "internally passive element"}@
			of b1 is also internally passive in b2.

			The internal order of an unordered matroid is computed with respect to the natural
			ordering on the ground set.
			Similarly, the internal order of a matrix is the internal order of the corresponding
			ordered vector matroid on the columns of the matrix.

		Example
			M = matroid sub(matrix {{1, 0, 1, 1, 0}, {-1, 1, 0, 0, 0}, {0, 0, -1, 0, 1}}, QQ);
			P = internalOrder M

		Text
			The duality between internally passive elements and @TO2{externallyActiveElements,
			"externally active elements"}@ induces an @TO isomorphism@ between the internal order
			of an ordered matroid and the poset dual of the @TO2 {externalOrder,
			"external order"}@ of the @TO2 {dualMatroid, "dual"}@ ordered matroid.

		Example
			areIsomorphic (P, dual externalOrder dualMatroid M)

		Text
			The rank generating function of the internal
			order of an ordered matroid gives the h-vector of the independence
			complex of the matroid.

		Example
			R = ZZ[x,y,q];
			p = sub(tuttePolynomial M,R);
			h = q^3*sub(p, {x => 1/q, y => 1}); -- the h-polynomial of M
			RGF = sub(rankGeneratingFunction internalOrder M,R);
			RGF == h
	SeeAlso
		externalOrder
		Posets
///

doc ///
	Key
		minimalBasis
		(minimalBasis, OrderedMatroid, List)
		(minimalBasis, Matroid, List)
	Headline
		compute the lex-minimal basis containing an independent set
	Usage
		B = minimalBasis(OM, I)
		B = minimalBasis(M, I)
	Inputs
		OM:OrderedMatroid
			an ordered matroid with linear order on the ground set E
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
		I:List
			a list of elements contained in some basis
	Outputs
		B:List
			the lexicographically least basis of an ordered matroid containing the elements in I.
	Description
		Text
			Every independent set of a matroid is contained in at least one basis.
			If the matroid is ordered, there is a unique lexicographically smallest such basis with the respect to the order.
			@TO2 {minimalBasis, "minimal basis"}@ return the list I is independent and throws an error otherwise.

		Example
			M = matroid sub(matrix {{1, 0, 1, 1, 0}, {-1, 1, 0, 0, 0}, {0, 0, -1, 0, 1}}, QQ);
			OM = orderedMatroid M;
			minimalBasis (orderedMatroid M, {0,3})
///

doc ///
    Key
        internalBasisDecomposition
        (internalBasisDecomposition, OrderedMatroid, List)
        (internalBasisDecomposition, Matroid, List)
    Headline
    	Internal Basis Decomposition
    Usage
    	internalBasisDecomposition(OM,B)
    	internalBasisDecomposition(M,B)
    Inputs
    	OM:OrderedMatroid
			an ordered matroid with linear order on the ground set E
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
    	B:List
    		a basis of the (ordered) matroid given as a list
    Outputs
    	D:List
    		a nested list
    Description
        Text
        	Let $B_0$ be the lexicographically least basis of an @TO2 {orderedMatroid, "ordered matroid"}@ and let B be any basis.
        	Then @TO internalBasisDecomposition@ returns the following partition of B: @BR{}@
        	(1) S is the set of  @TO2{internallyPassiveElements, "internally passive elements"}@ of B @EM "not in"@ $B_0$,@BR{}@
        	(2) T is the set of @TO2{internallyPassiveElements, "internally passive elements"}@ of B that @EM "are in"@ $B_0$, and @BR{}@
        	(3) A is the set of @TO2{internallyActiveElements, "internally active elements"}@ of B (necessarily in $B_0$).

        Example
        	M = matroid completeGraph 4;
        	OM1 = orderedMatroid (M, {0,1,2,3,4,5});
        	internalBasisDecomposition (OM1, {2,3,5})
        	OM2 = orderedMatroid (M, {5,4,3,2,1,0});
        	internalBasisDecomposition (OM2, {5,3,2})

///

doc ///
	Key
		basisType
		(basisType, OrderedMatroid, List)
		(basisType, Matroid, List)
	Headline
		compute the type of a basis
	Usage
		basisType(OM, B)
		basisType(M, B)
	Inputs
		OM:OrderedMatroid
			an ordered matroid
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
		B:List
			a basis of the matroid
	Outputs
		:String
			either "perfect" or "abundant" or "deficient"
	Description
		Text
			Write S, T, and A for the three lists obtained from the @TO2 {internalBasisDecomposition, "internal basis decomposition"}@ of the basis B.
			If S has a single element f, then B is called an f-principal basis.
			For f in S let B(f) be the @TO2 {minimalBasis, "minimal basis"}@ of S $\cup$ f and let T(f) be the elements of T that are also @TO2 {internallyPassiveElements, "internally passive elements"}@ of B(f).
			Then B is defined to be (internally) perfect if the sets T(f) form a partition of T.
			Equivalently, there is exactly one way to write B as the join of f-principal basis in the internal order of OM.

			If the union of all the T(f) equals T but is not a disjoint union, then B is called (internally) abundant.
			Equivalently, there is more than one way to write B as the join of f-principal bases.

			Finally, B is (internally) deficient if it is neither perfect nor abundant in which case there is no way to write B as the join of f-principal bases.

			Note that if T is empty or S is a singleton, then B is trivially perfect.
			For example, we compute the @TO2 {internalBasisDecomposition, "internal basis decomposition"}@ and @TO2 {basisType, "basis type"}@ of two bases of the complete graph on four vertices with the natural order on the ground set.

		Example
			OM = orderedMatroid matroid completeGraph 4;
			(internalBasisDecomposition(OM,{1,2,3}), basisType(OM,{1,2,3}))
			(internalBasisDecomposition(OM,{0,3,5}), basisType(OM,{0,3,5}))

		Text
			The ordered matroid above does have a deficient basis and an abundant basis.

		Example
			basisType (OM, {1,4,5})
			basisType (OM, {2,4,5})

	Caveat
		As usual, the @TO2 {basisType, "basis type"}@ of a basis of an ordered matroid will generally depend on @TO2 {orderedGround, "ordered ground"}@.
///

doc ///
	Key
		bjornersPartition
		(bjornersPartition, OrderedMatroid)
		(bjornersPartition, Matroid)
	Headline
		compute Bjorner's partition
	Usage
		bjornersPartition(OM)
		bjornersPartition(M)
	Inputs
		OM:OrderedMatroid
			an ordered matroid with linear order on the ground set E
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
	Outputs
		:List
			consisting of pairwise disjoint closed intervals in the boolean lattice on |E| elements
	Description
		Text
			For a basis B of an ordered matroid write EA(B) and IP(B) for the @TO2 {externallyActiveElements, "externally active"}@ and @TO2 {internallyPassiveElements, "internally passive elements"}@ of B, respectively.
			Bjorner proved that the intervals
			@BR{}@ @BR{}@
			[IP(B),B $\cup$ EA(B)]
			@BR{}@ @BR{}@
			in the boolean lattice on subsets of E form a partition, which we call Bjorner's partition.

		Example
			M = matroid sub(matrix {{1, 0, 1, 1, 0}, {-1, 1, 0, 0, 0}, {0, 0, -1, 0, 1}}, QQ);
			bp = bjornersPartition M
///

doc ///
	Key
		isInternallyPerfect
		(isInternallyPerfect, OrderedMatroid)
		(isInternallyPerfect, Matroid)
	Headline
		test if a matroid or ordered matroid is internally perfect
	Usage
		isInternallyPerfect(OM)
		isInternallyPerfect(M)
	Inputs
		OM:OrderedMatroid
			an ordered matroid with linear order on the ground set E
		M:Matroid
			a matroid with ground set E viewed as an ordered matroid via the natural ordering on E
	Outputs
		:Boolean
			whether a given matroid is internally perfect
	Description
		Text
			An @TO2{orderedMatroid, "ordered matroid"}@ is internally perfect if every basis is @TO2{basisType,"internally perfect"}@.
			By a result in [Da15], every internally perfect matroid
			 satisfies Stanley's conjecture on matroid h-vectors
			 since the internal order of such a matroid is
			 isomorphic to a pure multicomplex.

			An unordered matroid is internally perfect if there is some permutation of the ground set making it an internally perfect ordered matroid.

			Some ordered matroids are internally perfect for any reordering of the ground set. Examples include the graphic matroid of any cycle on n vertices and any matroid of rank no more than two.

		Example
			M = matroid cycleGraph 3;
			tally apply(permutations 3, p-> isInternallyPerfect orderedMatroid (M,p))

		Text
			Some ordered matroids are internally perfect for some reorderings but not for all. Consider the graphic matroid obtained from removing one edge from the complete graph on four vertices.

		Example
			M = matroid sub(matrix {{1, 0, 1, 1, 0}, {-1, 1, 0, 0, 0}, {0, 0, -1, 0, 1}}, QQ);
			isInternallyPerfect orderedMatroid M
			isInternallyPerfect orderedMatroid (M,{2,1,0})

		Text
			Since the matroid M above is internally perfect its internal order is isomorphic to a pure multicomplex.
			We provide one such in the following example.

		Example
			P = internalOrder orderedMatroid M;
			R = ZZ[x,y] -- define a polynomial ring
			I = monomialIdeal (x^3, x*y^2, y^4) -- define a monomial ideal in R;
			Q = standardMonomialPoset I;
			areIsomorphic(P,Q)

		Text
			The poset Q in the above example is the pure multicomplex consisting of all monomials that divide x^2*y and y^3.

			Finally, there are ordered matroids that are not internally perfect for any reordering of the ground set. Examples include the graphic matroid of the complete graph on n > 3 vertices and any uniform matroid U(r,n) where 2 < r < n-1.

		Example
			isInternallyPerfect matroid completeGraph 4
			isInternallyPerfect uniformMatroid(3,5)

		Text
			In particular, internally perfect matroids are not closed under duality. For example, we saw in the previous example that U(3,5) is not internally perfect. The dual matroid U(2,5) is a rank two matroid and so it is internally perfect (for any ordering of its ground set).

		Example
			M := uniformMatroid (3,5);
			tally apply(permutations 5, p -> isInternallyPerfect orderedMatroid(dualMatroid M, p))

		Text
			@BR{}@ @BR{}@
			{\bf References}@BR{}@
			@UL{
				"[Da15] Internally Perfect Matroids  (Dall,
				2015)",
				}@
///
--'
doc ///
	Key
		matroidHVector
		(matroidHVector, Matroid)
	Headline
		compute the h-vector of the independence complex of a matroid
	Usage
		matroidHVector(M)
	Inputs
		M:Matroid
	Outputs
		:List
			a list of length rank M + 1
	Description
		Text
			The independent sets I of a matroid M = (E,I) form an abstract simplicial complex $\Delta = \Delta$(M), called the independence complex of M. This complex is also known as the independent set complex or the matroid complex of M.
			The h-vector of a matroid is the h-vector of $\Delta$.
			Since $\Delta$ is partitionable (indeed, shellable) for any matroid it follows that the h-vector of $\Delta$ is a sequence of nonnegative integers of length rank M + 1.

		Example
			M = matroid sub(matrix {{1, 0, 1, 1, 0}, {-1, 1, 0, 0, 0}, {0, 0, -1, 0, 1}}, QQ);
			matroidHVector M

		Text
			For each @TO2 {coloops, "coloop"}@ of M the h-vector will have a trailing zero.

		Example
			matroidHVector uniformMatroid (1,1)
			matroidHVector uniformMatroid (2,2)
			matroidHVector uniformMatroid (3,3)

	Caveat
		This method uses @TO tuttePolynomial@ from the package
		@TO Matroids@ to compute the h-vector. As for any
		simpicial complex, one may also compute the h-vector
		from the f-vector of the matroid complex whose entries
		encode the number of independent sets of each cardinality.
		Note that this definition of the f-vector of a matroid is
		not the same as that used for the method @TO fvector@ in
		the @TO Matroids@ package.
///

doc ///
	Key
		texActiveOrder
		(texActiveOrder, Poset)
		[texActiveOrder, Jitter]
	Headline
		An improved tex output for active orders
	Usage
		texActiveOrder(P)
		texActiveOrder(P, Jitter => Boolean)
	Inputs
		P:Poset
		Jitter=>Boolean
			whether to randomly jitter the poset vertices
	Outputs
		:String
			a tikz string for exporting into TeX files
	Description
		Text
			@TO texActiveOrder@ outputs a TeX string for
			a poset that closely mimicks the method @TO texPoset@
			from the package @TO Posets@, but with modifications to
			the layout that greatly increase readablitiy of the string
			and the resulting rendering of the poset. Compare the following:

		Example
			texActiveOrder internalOrder matroid completeGraph 3
			texPoset internalOrder matroid completeGraph 3

	Caveat
		@TO texActiveOrder@ may be called on any poset whose
		@TO2{GroundSet, "ground set"}@ has elements similar to those
		of the ground set of the @TO2{externalOrder,"external"}@ or
		@TO2{internalOrder,"internal order"}@ of a matroid. Results may vary.
///

doc ///
	Key
		(net,OrderedMatroid)
	Usage
		net(M)
	Inputs
		M:OrderedMatroid
	Outputs
		:Net
	Description
		Text
			Shortens default output for an object of type OrderedMatroid.
		Example
			net orderedMatroid matroid completeGraph 3
///

-- End exported documentation --

-- Begin Tests --
TEST ///
-- orderedGround
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(M.orderedGround === {1,2,0})
///

TEST ///
--orderedBases
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(M.orderedBases === {{1, 2}, {1, 0}, {2, 0}})
///

TEST ///
--orderedCircuits
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(M.orderedCircuits === {{1,2,0}})
///

TEST ///
--orderedCocircuits
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(M.orderedCocircuits === {{1, 0}, {2, 0}, {1, 2}})
///

TEST ///
-- orderedFlats
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(orderedFlats M === {{{}}, {{2}, {1}, {0}}, {{1, 2, 0}}})
///

TEST ///
-- activeElements
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(activeElements (M,{1,2}) === {})
///

TEST ///
-- duallyActiveElements
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(duallyActiveElements(M,{1,2}) === {1,2})
///

TEST ///
-- externallyActiveElements
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(externallyActiveElements(M,{1,2}) === {})
///

TEST ///
-- externallyPassiveElements
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(externallyPassiveElements (M,{1,2}) === {0})
///

TEST ///
-- internallyActiveElements
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(internallyActiveElements (M,{1,2}) === {1,2})
///

TEST ///
-- internallyPassiveElements
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(internallyPassiveElements (M,{1,2}) === {})
///

TEST ///
-- externalOrder
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(areIsomorphic(externalOrder M, dual internalOrder orderedMatroid(dualMatroid M.matroid, {1,2})) === true)
///

TEST ///
-- internalOrder (see externalOrder test)
///

TEST ///
-- minimalBasis
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(minimalBasis(M,{1}) === {1,2})
///

TEST ///
-- internalBasisDecomposition
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(internalBasisDecomposition(M,{1,2}) === {{},{},{1,2}})
///

TEST ///
--  basisType
M = orderedMatroid (matroid completeGraph 4,{1,2})
assert(basisType(M,{1,2,0}) === "perfect")
assert(basisType(M,{0,3,4}) === "abundant")
assert(basisType(M,{2,3,4}) === "deficient")
///

TEST ///
-- bjornersPartition
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(bjornersPartition(M) === {[{}, {1, 2}], [{0}, {1, 0}], [{2, 0}, {1, 2, 0}]})
///

TEST ///
-- parallelClasses
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(parallelClasses M === {set {2}, set {1}, set {0}})
///

TEST ///
-- matroidHVector
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(matroidHVector M.matroid === {1,1,1})
///

TEST ///
-- texActiveOrder
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(class texActiveOrder internalOrder M === Nothing)
///

TEST ///
-- isActive
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(isActive(M,{1,2},2) === false)
///

TEST ///
-- isDuallyActive
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(isDuallyActive(M,{1,2},2) === true)
///

TEST ///
-- isInternallyPerfect
M = orderedMatroid (matroid completeGraph 3,{1,2})
assert(isInternallyPerfect M === true)
///
-- End Tests --
end

restart
load "randomMatrix.m2"
uninstallPackage "MatroidActivities"
installPackage "MatroidActivities"
viewHelp texActiveOrder
check "MatroidActivities"
loadPackage("MatroidActivities", Reload => true)
M1 = matroid sub(matrix{{1,0,1,1,0},{-1,1,0,0,0},{0,0,-1,0,1}},QQ);
OM1 = orderedMatroid (M,{0,1,2,3,4})
OM11 = orderedMatroid (M,{0,2,1,3,4})
M2 = matroid completeGraph 4
OM2 = orderedMatroid M
OM22 = orderedMatroid (M,{5,4,3,2,1,0})
