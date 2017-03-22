-- -*- coding: utf-8 -*-
--  MatroidActivities.m2
--
--  Copyright (C) 2016 Aaron Dall <aaronmdall@gmail.com>
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  This program is free software; you can redistribute it
--  and/or modify  it under the terms of the GNU General
--  Public License as   published by  the Free Software Found-
--  ation; either version 2 of the License, or (at  your
--  option) any later version.
--
--  This program is distributed in the hope that it will be
--  useful, but  WITHOUT ANY WARRANTY; without even the
--  implied warranty of  MERCHANTABILITY or FITNESS FOR A
--  PARTICULAR PURPOSE.  See the GNU  General Public License
--  for more details.
--
--  You should have received a copy of the GNU General
--  Public License along with this program; if not, write
--  to the Free Software Foundation, Inc.,  59 Temple Place,
--  Suite 330, Boston, MA 02111-1307 USA.
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  Release 0.2 (2017 03)
--      NEW:
--          Methods for constructing a matroid from an ideal, simplicial 
--          complex, or central arrangement; 
--          Methods for constructing the face ring, Chow ring, and 
--          Orlik-Solomon algebra of a matroid or ordered matroid; 
--          Test if a matroid is simple, binary, ternary, (co)graphic, 
--          regular, or paving;
--          Split the TikZ rendering of active orders into two methods for 
--          improved rendering.
--      BUGS FIXED: 
--          Fixed a list bug in the internalOrder code which was causing a 
--          problem with the isInternallyPerfect method;
--          Fixed a TikZ rendering problem when trying to tex active orders on 
--          matroids with more than 9 elements.
--
--  Release 0.1 (2016 07 24)
--      NEW: the class OrderedMatroid and methods bjornersPartition, 
--      matroidHVector, externalOrder, internalOrder, isInternallyPerfect, 
--      texActiveOrder
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
newPackage (
    "MatroidActivities",
    Version => "0.2", 
    Date => "2017 03 01",
    Authors => {{
        Name => "Aaron Dall",
        Email => "aaronmdall -at- gmail.com",
        HomePage => "https://github.com/aarondall/MatroidActivities-M2"}},
    PackageExports => {
        "HyperplaneArrangements",
        "Posets", 
        "SimplicialComplexes", 
        "Depth",
        "Matroids"},
    Headline => "MatroidActivities",
    DebuggingMode => false
    )

export {
-- INTERNAL FUNCTIONS --
    --"relativeOrder", -- internal function
    --"monomialToList", -- internal function
    --"listToTexString", -- internal function
-- ORDERED MATROID FUNCTIONALITY --
    "OrderedMatroid", -- documented type
    "orderedMatroid", -- documented method
    "orderedBases", -- documented key
    "orderedCircuits", -- documented key
    "orderedCocircuits", -- documented key
    "orderedGround", -- documented key
    "orderedFlats", -- documented method
    "activeElements", -- documented method
    "duallyActiveElements", -- documented method
    "externallyActiveElements", -- documented method
    "externallyPassiveElements", -- documented method
    "internallyActiveElements", -- documented method
    "internallyPassiveElements", -- documented method
    "externalOrder", -- documented method
        "ShowExt", -- documented option
    "internalOrder", -- documented method
    "minimalBasis", -- documented
    "internalBasisDecomposition", -- documented
    "basisType", -- documented
    "bjornersPartition", -- documented
    "matroidOrlikSolomon", -- documented method
    "brokenCircuitComplex", -- undocumented
    "texExternalOrder", -- undocumented
    "texInternalOrder", -- undocumented
    "isActive", -- documented
    "isDuallyActive", -- documented
    "isInternallyPerfect", -- documented method
    "IsInternallyPerfect", -- undocumented key
-- MATROID FUNCTIONALITY --
--    "circuitIdeal", --undocumented method
    "CircuitIdeal", -- undocumented key
    "IndependenceComplex", -- undocumented key 
    "isRepresentableMatroid", -- undocumented test
    "Presentations", -- undocumented key
    "latticeOfFlats", -- documented method
        "Reduced", -- option
    "LatticeOfFlats", --undocumented key
    "parallelClasses", -- documented
    "matroidIndependenceComplex", --undocumented    
        "ComputePoset", -- option
        "complexAsPoset", -- key in simplicial complex cache
    "matroidTuttePolynomial", -- documented
    "matroidHPolynomial", -- documented
    "matroidFVector", -- documented
    "betaInvariant", -- undocumented
    "matroidChowIdeal", -- documented   
    "matroidChowRing", --documented
    "matroidCharacteristicPolynomial", --undocumented
    -- Tests --
    "isBinaryMatroid", --undocumented method
    "IsBinaryMatroid", --undocumented key
    "isCographicMatroid", --undocumented method
    "IsCographicMatroid", --undocumented key
    "isGraphicMatroid", --undocumented method
    "IsGraphicMatroid", --undocumented key
    "isPavingMatroid", --undocumented method
    "IsPavingMatroid", --undocumented key
    "isRegularMatroid", --undocumented method
    "IsRegularMatroid", --undocumented key
    "IsRepresentableMatroid", --undocumented 
    "isSimpleMatroid", --undocumented method
    "IsSimpleMatroid", --undocumented key
    "isTernaryMatroid", --undocumented method
    "IsTernaryMatroid", --undocumented key
-- GRAPH FUNCTIONALITY --
    "signedIncidenceMatrix", -- undocumented method
        "FullRank", -- undocumented option
-- SIMPLICIAL COMPLEX FUNCTIONALITY 
    "isMatroidIndependenceComplex" --undocumented method
    }

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

--  INTERNAL METHODS --

-- A method for ordering sets and (lists of) lists with respect to a given list
-- Elements in the intersection come first with order induced from L
-- Elements in A not in L come later with the order induced by sort

relativeOrder = method(TypicalValue => List)
-- For a set S, assumes all elements are single elements all belonging to the 
-- same class having some method for comparison (see: viewHelp "?") 
relativeOrder (Set, List) := (S, L) -> (    
    if S === set {} then toList {} else
    SL := select(L, l -> member(l,S));
    B := if SL === null then {} else SL;
    notSL := select(toList S, s -> not member(s,L));
    C := if notSL === null then {} else notSL;
    B | sort C)

-- For a list L1, assumes each element is a VisibleList consisting of elements
-- that are also visible lists such that all elements of flatten L1 are of
-- the type ZZ
relativeOrder (List, List) := (L1,L2) -> (
    -- First convert all elements of L1 into Lists sorted by sort.
    M1 := apply (L1, l -> sort toList l);
    -- Next order all the elements appearing in the union of M1 according
    -- to L2.
    M2 := relativeOrder (set unique flatten M1, L2);
    orderEach := apply (
        M1, 
        l -> (
            n := #l;
            rel := relativeOrder (set l, M2);
            {apply (n, i -> position (M2, e -> e == rel#i)), 
            rel}
            )
        );
    apply(sort orderEach, l -> l#1))    

-- Compute the signed incidence matrix of a graph G.
-- This matrix represents the matroid of G over any field, is fast to produce 
-- (K60 takes about a second), and allows for easily adding edges with 
-- multiplicities.
signedIncidenceMatrix = method (
    TypicalValue => Matrix,
    Options => {FullRank => true})
signedIncidenceMatrix Graph := Matrix => opts -> G -> (
    M := matrix table (
        vertices G, --
        apply(edges G, e -> sort toList e), 
        (v,e) -> if not member(v,e) 
                then 0 
            else if v == first e then 1 else -1);
    if not opts.FullRank then M else submatrix' (M, {numRows M -1}, {}))    

-- Convert a monomial in a polynomial ring to its support given as a list of 
-- indices of variables. Used in converting a simplicial complex to a matroid
-- if the complex is a matroid complex. 
monomialToList = method(TypicalValue => List)
monomialToList RingElement := m -> (
    R := ring m;
    apply(support m, var -> index var)
    )

-- Internal methods for converting between strings and lists.
-- Used to beautify tex output of posets
listToTexString = L -> concatenate apply (
    L, l -> (
        if class l =!= ZZ
            then toString l
        else if l < 10
            then toString  l
        else concatenate("\\underline{", toString l, "}")))

-- ORDERED MATROID FUNCTIONALITY --

-- Setting up the OrderedMatroid Type
OrderedMatroid = new Type of HashTable

-- set output for OrderedMatroid
globalAssignment OrderedMatroid
net OrderedMatroid := X -> (
    if hasAttribute(X, ReverseDictionary) 
        then toString getAttribute(X, ReverseDictionary)
    else "OrderedMatroid"
)

-- OrderedMatroid equality
OrderedMatroid == OrderedMatroid := (M, N) ->  (
    isomorphic (M.matroid, N.matroid) and
    all(M.orderedGround, N.orderedGround, (i,j) -> rk_(M.matroid) {i,j}==1)
    )

--  Make an ordered matroid from an ordered subset of the
--  ground set

orderedMatroid = method(TypicalValue => OrderedMatroid)
orderedMatroid (Matroid, List) := (M,L) -> (
    r := rk M;
    E := relativeOrder(M.ground, L);
    n := #E;
    B := relativeOrder(M.bases, E);
    Ci := relativeOrder(circuits M, E);
    Coci := relativeOrder(circuits dualMatroid M, E);
    OM := new OrderedMatroid from {
        symbol matroid => M,
        symbol orderedGround => E,
        symbol orderedBases => B,
        symbol orderedCircuits => Ci,
        symbol orderedCocircuits => Coci,
        symbol Presentations => new CacheTable,
        cache => new CacheTable
    };
    OM
)
orderedMatroid (Matroid) := M -> (orderedMatroid (M, {}))

orderedMatroid (Matrix, List) := (M, L) -> (
    OM := orderedMatroid (matroid M, L);
    OM.Presentations.Matrix = M_L;
    OM.cache.isRepresentableMatroid = 
        if isField ring M 
            then true 
        else "Unknown. Matrix over a ring that is not a field.";
    OM)
orderedMatroid (Matrix) := M -> orderedMatroid (M, toList(0..<numColumns M))

orderedMatroid (Graph, List) := (G, L) -> (
    N := signedIncidenceMatrix G;
    OM := orderedMatroid (N, L);
    OM.Presentations.Graph = G;
    OM.cache.isGraphicMatroid = true;
    OM.cache.isRepresentableMatroid = true;
    OM.cache.isRegular = true;
    OM)
orderedMatroid (Graph) := G -> orderedMatroid (G, toList(0..<# edges G))

orderedMatroid (CentralArrangement, List) := (A, L) -> (
    R := coefficientRing ring A;
    S := if isField R then R 
            else if R == ZZ then QQ 
            else error "expected a field or ZZ";
    M := sub(coefficients A, S);        
    OM := orderedMatroid (M, L);
    OM.Presentations.CentralArrangement = A;
    OM.Presentations.Matrix = M;
    OM.cache.isRepresentableMatroid = true;
    OM)
orderedMatroid (CentralArrangement) := A -> (
    orderedMatroid (A, toList(0..<numColumns coefficients A)))

orderedMatroid (SimplicialComplex, List) := (C, L) -> (
    if not isPure C then error "Complex is not matroidal (not pure)" else
    F := flatten entries facets C;
    B := apply (F, m -> monomialToList m);
    M := matroid B;
    if not isValid M 
        then error "Complex is not matroidal (basis exchange axiom not satisfied)"
    else    
        OM := orderedMatroid (M, L);
        OM.Presentations.IndependenceComplex = C; 
        OM
    )
orderedMatroid (SimplicialComplex) := C -> (orderedMatroid (C, {})) 

orderedMatroid (Ideal, List) := (I, L) -> (
    if I =!= monomialIdeal I
        then error "Expected a monomial ideal; try monomialIdeal (I) or monomialSubideal (I)"
    else if not isSquareFree I
        then error "Expected a square free ideal; try radical I"
    else 
        OM := orderedMatroid (simplicialComplex I, L);
        if instance (OM, OrderedMatroid)
            then OM.Presentations.CircuitIdeal = I;
        OM)
orderedMatroid  (Ideal) := I -> orderedMatroid (I,{})

-- ORDERED ANALOGUES OF MATROIDAL OBJECTS NOT YET CONSTRUCTED
-- Must convert a matroid, matrix, graph, etc to an ordered matroid first
orderedFlats = method()
orderedFlats OrderedMatroid := M -> (
    apply(
        flats M.matroid, 
        L -> apply (L, f->  relativeOrder(f, M.orderedGround)))
        )

-- MATROID ACTIVITIES
--  Test if an element of an ordered matroid is active with respect to a set --
isActive = method(TypicalValue => Boolean)
isActive (OrderedMatroid, List, ZZ) := (M, A, e) -> (
    any (M.orderedCircuits, c -> e == first c and isSubset(c, append(A,e))))

--  Test if an element of an ordered matroid is active in the dual 
--  matroid with respect to a set
isDuallyActive = method(TypicalValue => Boolean)
isDuallyActive (OrderedMatroid, List, ZZ) := (M, A, e) -> (
    any (
        M.orderedCocircuits, 
        c -> e == first c and isSubset (
            c, 
            append(select(M.orderedGround, f -> not member(f,A)),e)
            )
        )
    )

activeElements = method(TypicalValue=>List)
activeElements (OrderedMatroid, List) := List => (M, A) -> (
    if not isSubset(A, M.orderedGround)
        then error "expected a subset of the ground set"
    else
        select(M.orderedGround, e -> isActive(M, A, e)))

duallyActiveElements = method(TypicalValue=>List)
duallyActiveElements (OrderedMatroid, List) := List => (M, A) -> (
    if not isSubset(A, M.orderedGround)
        then error "expected a subset of the ground set"
    else
        select(M.orderedGround, e -> isDuallyActive(M, A, e)))

externallyActiveElements = method(TypicalValue => List)
externallyActiveElements (OrderedMatroid, List) := List => (M,A) ->(
    relativeOrder (set activeElements(M,A) - set A, M.orderedGround))

externallyPassiveElements = method(TypicalValue => List)
externallyPassiveElements (OrderedMatroid, List) := List => (M,A) -> (
    relativeOrder ((set M.orderedGround - set activeElements(M,A)) - set A, M.orderedGround))

internallyActiveElements = method (TypicalValue => List)
internallyActiveElements (OrderedMatroid, List) := List => (M,A) -> (
    relativeOrder (set A * set duallyActiveElements(M,A), M.orderedGround)
    )

internallyPassiveElements = method (TypicalValue => List)
internallyPassiveElements (OrderedMatroid, List) := List =>  (M,A) ->(
    relativeOrder (set A - set internallyActiveElements(M,A),M.orderedGround))

externalOrder = method (
    TypicalValue => Poset,
    Options => {symbol ShowExt => false})
externalOrder OrderedMatroid := Poset => opts -> M -> (
    h := hashTable apply(M.orderedBases, b -> b => externallyActiveElements(M,b));
    cmp := (a,b) -> isSubset(a#0, join(b#0,h#(b#0)));
    cmp1 := (a,b) -> isSubset(a, join(b,h#(b)));
    if opts.ShowExt == true 
        then poset (apply(M.orderedBases, b-> {b,h#(b)}),cmp)
    else poset (M.orderedBases,cmp1))

internalOrder = method(TypicalValue => Poset)
internalOrder OrderedMatroid := Poset => M -> (
    h1 := hashTable apply(M.orderedBases, b -> b => internallyPassiveElements(M,b));
    cmp := (a,b) -> (
        isSubset(
            h1#(relativeOrder (set flatten a, M.orderedGround)),
            h1#(relativeOrder (set flatten b,M.orderedGround)))
        );
    poset(apply(M.orderedBases, b -> internalBasisDecomposition(M,b)), cmp))

--compute the minimal basis containing an independent set
minimalBasis = method(TypicalValue => List)
minimalBasis (OrderedMatroid, List) := List => (M, I) -> (
    p := (position(M.orderedBases, b -> isSubset(I, b)));
    if class p === ZZ then (M.orderedBases)#p else error "expected an independent set")

internalBasisDecomposition = method(TypicalValue => List)
internalBasisDecomposition (OrderedMatroid, List) := List => (M, b) -> (
    B0 := first M.orderedBases;
    IA := internallyActiveElements (M, b);
    IP := internallyPassiveElements (M, b);
    S := relativeOrder (set IP - set B0, M.orderedGround);
    T := relativeOrder (set IP - S, M.orderedGround);
    {S,T,IA})


basisType = method()
basisType (OrderedMatroid,List) := (M,b) -> (
    (S,T,A):= toSequence internalBasisDecomposition(M,b);
    -- make the multiset of provisionally passive elements
    projections := flatten for f in S list (
        newBs := minimalBasis(M, append(T,f));
        (internalBasisDecomposition(M,newBs))#1);
    -- check if the multiset is a disjoint union and covers T
    if sort projections == sort T
        then "perfect"
    -- check if the multiset covers T
    else if sort unique projections == sort T
        then "abundant"
    else "deficient"
    )


isInternallyPerfect = method(TypicalValue => Boolean)
isInternallyPerfect (OrderedMatroid) := Boolean => (M) -> (
    if M.cache.?IsInternallyPerfect then M.cache.IsInternallyPerfect else
    topElements := apply(maximalElements internalOrder M, b -> flatten b);
    check := b -> basisType(M,flatten b) == "perfect";
    Bool := all(topElements, check);
    M.cache.IsInternallyPerfect = Bool;
    Bool
    )
-- Test if any permutation makes a matroid into an internally perfect matroid
isInternallyPerfect Matroid := Boolean => M -> (
    B := sort apply (M.bases, b -> sort toList b);
    checkPermsOfBasis := b -> (
        P := permutations toList b;
        k := position(P, p-> isInternallyPerfect orderedMatroid (M, p));
        if class k === ZZ then P#k else null
        );
    j := (position(B, b -> checkPermsOfBasis b =!= null));
    if class j === ZZ then (print checkPermsOfBasis (B)#j);
    return class j === ZZ
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

--  ADDITIONAL UNORDERED MATROID FUNCTIONALITY --

-- Properties independent of the ordering of a matroid stored in 
-- OM.matroid.cache

isSimpleMatroid = method (TypicalValue => Boolean)
isSimpleMatroid Matroid := M -> (
    if M.cache.?IsSimpleMatroid
        then return M.cache.IsSimpleMatroid
    else    
    check := # loops M == 0 and all (flats (M, 1), f -> #f == 1);
    M.cache.IsSimpleMatroid = check;
    check)
isSimpleMatroid OrderedMatroid := M -> (
    isSimpleMatroid M.matroid)

------------------------------------------
-- matroid classes
------------------------------------------

-- Internal hash of forbidden minors for certain classes of matroids
-- Extend this as much as possible 
ForbiddenMinors = new HashTable from {
    "binaryMatroids" => {uniformMatroid(2,4)},
    "ternaryMatroids" => {
        uniformMatroid(2,5),
        uniformMatroid(3,5),
        specificMatroids "fano",
        dualMatroid specificMatroids "fano"},
    "graphicMatroids" => {
        uniformMatroid(2,4),
        specificMatroids "fano",
        dualMatroid specificMatroids "fano",
        dualMatroid matroid completeGraph 5,
        dualMatroid matroid completeMultipartiteGraph {3,3}},
    "cographicMatroids" => {
        uniformMatroid(2,4),
        specificMatroids "fano",
        dualMatroid specificMatroids "fano",
        matroid completeGraph 5,
        matroid completeMultipartiteGraph {3,3}},
    "regularMatroids" => {
        uniformMatroid(2,4),
        specificMatroids "fano",
        dualMatroid specificMatroids "fano"}    
    }

isBinaryMatroid = method(TypicalValue => Boolean)
isBinaryMatroid Matroid := M -> (
    if M.cache.?IsBinaryMatroid 
        then return M.cache.IsBinaryMatroid 
    else
    check := not any (
        ForbiddenMinors#"binaryMatroids", 
        N -> hasMinor (M,N));
    M.cache.IsBinaryMatroid = check;
    if check == true then
        M.cache.IsRepresentableMatroid = check;
    check)
isBinaryMatroid OrderedMatroid := M -> (
    isBinaryMatroid M.matroid)  

isTernaryMatroid = method(TypicalValue => Boolean)
isTernaryMatroid Matroid := M -> (
    if M.cache.?IsTernaryMatroid 
        then return M.cache.IsTernaryMatroid 
    else
    check := not any(ForbiddenMinors#"ternaryMatroids", N -> hasMinor(M,N));
    M.cache.IsTernaryMatroid = check;
    if check then
        M.cache.IsRepresentableMatroid = check;
    check)
isTernaryMatroid OrderedMatroid := M -> (
    isTernaryMatroid M.matroid) 

isGraphicMatroid = method(TypicalValue => Boolean)
isGraphicMatroid Matroid := M -> (
    if M.cache.?IsGraphicMatroid 
        then return M.cache.IsGraphicMatroid 
    else
    check := not any(ForbiddenMinors#"graphicMatroids", N -> hasMinor(M,N));
    M.cache.IsGraphicMatroid = check;
    if check then (
        M.cache.IsRepresentableMatroid = true,
        M.cache.IsRegularMatroid = true);
    check)
isGraphicMatroid OrderedMatroid := M -> (
    isGraphicMatroid M.matroid)     

isCographicMatroid = method(TypicalValue => Boolean)
isCographicMatroid Matroid := M -> (
    if M.cache.?IsCographicMatroid 
        then return M.cache.IsCographicMatroid 
    else
    check := not any(
        ForbiddenMinors#"cographicMatroids", 
        N -> hasMinor(M,N));
    M.cache.IsCographicMatroid = check;
    if check then (
        M.cache.IsRepresentableMatroid = check,
        M.cache.IsRegularMatroid = check);
    check)
isCographicMatroid OrderedMatroid := M -> (
    isCographicMatroid M.matroid)       

isRegularMatroid = method(TypicalValue => Boolean)
isRegularMatroid Matroid := M -> (
    if M.cache.?IsRegularMatroid 
        then return M.cache.IsRegularMatroid else
    check := not any(
        ForbiddenMinors#"regularMatroids", 
        N -> hasMinor(M,N));
    M.cache.IsRegularMatroid = check;
    if check then (
        M.cache.IsRepresentableMatroid = check,
        M.cache.IsBinaryMatroid = check,
        M.cache.IsTernaryMatroid = check);
    check)
isRegularMatroid OrderedMatroid := M -> (
    isRegularMatroid M.matroid) 

isRepresentableMatroid = method (TypicalValue => Boolean)
isRepresentableMatroid Matroid := M -> (
    if M.cache.?IsRepresentableMatroid
        then return M.cache.IsRepresentableMatroid
    else 
        try isomorphic (M, matroid matrix {M.groundSet})
            then (
                check := isomorphic (M, matroid matrix {M.groundSet});
                if check == true
                    then (
                        M.cache.IsRepresentableMatroid = true;
                        return check)
                else print "Unknown. Try isBinaryMatroid, isTernaryMatroid, etc.";)
        else print "Unknown. Try isBinaryMatroid, isTernaryMatroid, etc.";
    )
isRepresentableMatroid OrderedMatroid := M -> (
    isRepresentableMatroid M.matroid)       

isPavingMatroid = method(TypicalValue => Boolean)
isPavingMatroid Matroid := M -> (
    if M.cache.?IsPavingMatroid 
        then return M.cache.IsPavingMatroid 
    else
    r := rk M;
    check := all(
        circuits M, 
        c -> member (#c, {r, r+1}));
    M.cache.IsPavingMatroid = check;
    check)
isPavingMatroid OrderedMatroid := M -> (
    isPavingMatroid M.matroid
    )

latticeOfFlats = method (
    Options => {symbol Reduced => true},
    TypicalValue => Poset)
latticeOfFlats Matroid := Poset => opts -> M -> (
    if M.cache.?LatticeOfFlats and opts.Reduced == true
        then return M.cache.LatticeOfFlats
    else    
    F := sort apply (flatten flats M, f -> sort toList f);
    P := poset (F, isSubset);
    reduceP := P - join (maximalElements P, minimalElements P);
    M.cache.LatticeOfFlats = reduceP;
    if opts.Reduced == false 
        then P
    else reduceP)
latticeOfFlats OrderedMatroid := Poset => opts -> M -> (
    latticeOfFlats (M.matroid, Reduced => opts.Reduced))

parallelClasses = method(TypicalValue => List)
parallelClasses Matroid := M -> (
    select(flatten flats M, f -> rk_M f == 1))
parallelClasses OrderedMatroid := OM -> (
    select(flatten orderedFlats OM, f -> rk_(OM.matroid) f == 1))


matroidIndependenceComplex = method (
    TypicalValue => SimplicialComplex,
    Options => {symbol ComputePoset => false})
matroidIndependenceComplex (Matroid, Ring) := SimplicialComplex => opts -> (M, R) -> (
    if M.cache.?IndependenceComplex 
        then return  M.cache.IndependenceComplex 
    else    
    E := toList M.ground;
    B := sort apply (M.bases, b -> sort toList b);
    x := getSymbol "x";
    S := R (
        monoid [apply (E, e -> x_e), 
        Weights => toList(0..<#E)]); 
    monomialsFromBases := apply(
        B, b -> product apply(b, e -> S_e));
    C := simplicialComplex monomialsFromBases;
    M.cache.CircuitIdeal = C.faceIdeal;
    M.cache.IndependenceComplex = C;
    if not opts.ComputePoset then C else
    M.cache.complexAsPoset = poset (
        unique flatten apply (B, b -> subsets b), 
        isSubset);
    C)
matroidIndependenceComplex Matroid := SimplicialComplex => opts -> M -> (
    matroidIndependenceComplex (M, QQ, ComputePoset => opts.ComputePoset))
matroidIndependenceComplex (OrderedMatroid, Ring) := SimplicialComplex => opts -> (M,R) -> (
        E := M.orderedGround;
        B := M.orderedBases;
        x := getSymbol "x";
        S := R (
            monoid[apply(E, e -> x_e), 
            Weights => toList(0..<#E)]);
        monomialsFromBases := apply(B, b -> product apply(b, e -> S_e));
        C := simplicialComplex monomialsFromBases;
        M.Presentations.CircuitIdeal = C.faceIdeal;
        M.Presentations.IndependenceComplex = C;
        if opts.ComputePoset == false then C else 
        M.Presentations.complexAsPoset = poset (
            unique flatten apply (B, b -> subsets b), 
            isSubset);
        C)  
matroidIndependenceComplex OrderedMatroid := SimplicialComplex => opts -> M -> (
    matroidIndependenceComplex (M,QQ, ComputePoset => opts.ComputePoset))       

isMatroidIndependenceComplex = method (TypicalValue => Boolean)
isMatroidIndependenceComplex SimplicialComplex := C -> (
    if not isPure C then (
        print "Complex is not matroidal (not pure)";   
        return false;)
    else
    F := flatten entries facets C;
    B := apply (F, m -> monomialToList m);
    M := matroid B;
    if not isValid M then (
        print ("Complex is not matroidal (basis exchange axiom not satisfied)");
        return false;)
    else true)

--circuitIdeal = method (TypicalValue => MonomialIdeal)
--circuitIdeal (Matroid, Ring) := (M, R) -> (
--    if M.cache.?CircuitIdeal then M.cache.CircuitIdeal 
--    else 
--    )

matroidTuttePolynomial = method(TypicalValue => RingElement)
matroidTuttePolynomial OrderedMatroid := M -> (
    R := ZZ(monoid[getSymbol "x", getSymbol "y"]);
    sum apply(
        M.orderedBases, 
        b -> R_0^(#internallyActiveElements(M,b)) 
            * R_1^(#externallyActiveElements(M,b)))
    )
matroidTuttePolynomial Matroid := M -> matroidTuttePolynomial orderedMatroid M

matroidHPolynomial = method(TypicalValue => RingElement)
matroidHPolynomial Matroid := M -> (
    h := numerator reduceHilbert hilbertSeries (matroidIndependenceComplex M).faceIdeal;
    R := ZZ(monoid[getSymbol "T", getSymbol "q"]);
    S := ZZ(monoid[getSymbol "q"]);
    sub(sub(sub(h,R), R_0 => R_1),S)
    )
matroidHPolynomial OrderedMatroid := M -> (
    matroidHPolynomial M.matroid)    

matroidFVector = method (TypicalValue => HashTable)
matroidFVector Matroid := M -> (
    fVector matroidIndependenceComplex M)
matroidFVector OrderedMatroid := M -> (matroidFVector M.matroid)

betaInvariant = method (TypicalValue => ZZ)
betaInvariant Matroid := M -> (
    r := rk M;
    E := M.ground;
    (-1)^r * sum for s in subsets E list (
        (-1)^(#s)*rk(M,s))
    )
betaInvariant OrderedMatroid := M -> betaInvariant M.matroid

matroidChowIdeal = method (TypicalValue => Ideal)
matroidChowIdeal (Matroid, Ring) := Ideal => (M, R) -> (
    E := toList M.ground;
    P := latticeOfFlats M;
    S := R (monoid [apply (P.GroundSet, f -> (getSymbol "x")_f)]);
    I := ideal unique flatten table (
        P.GroundSet, 
        P.GroundSet, 
        (f, g) -> if compare (P, f, g) 
            then 0_S 
        else S_((value "x")_f) * S_((value "x")_g)
        );
    h := hashTable apply (E, e -> e => delete (
            null, 
            apply (P.GroundSet, f -> if member (e, f) then f else null)
            )
        );
    J := ideal unique flatten table (
        E, 
        E, 
        (a,b) -> sum apply (h#a, f -> S_((value "x")_f)) - sum (h#b, f-> S_((value "x")_f))
        );
    I + J)
matroidChowIdeal Matroid := Ideal => M -> (
    matroidChowIdeal (M, QQ))   

matroidChowRing = method (TypicalValue => QuotientRing)
matroidChowRing (Matroid, Ring) := QuotientRing => (M, R) -> (
    I := matroidChowIdeal (M, R);
    ring I / I
    )   
matroidChowRing Matroid := QuotientRing => M -> (
    I := matroidChowIdeal M;
    ring I / I
    )

matroidOrlikSolomon = method (TypicalValue => QuotientRing)
matroidOrlikSolomon OrderedMatroid := QuotientRing => M -> (
    e := symbol e;
    R := ZZ (monoid [
        apply (M.orderedGround, f -> e_f), -- a variable for each f in E
        MonomialOrder => { -- set the order of the variables
            Weights => toList (0..<#M.orderedGround),
            GLex},  --use graded lex as a tie-breaker
        SkewCommutative => true -- work in the exterior algebra
        ]);
    I := ideal apply (
        M.orderedCircuits, 
        C -> sum apply(
            toList(0..<#C), 
            i -> (-1)^i * product apply(
                delete(C#i,C), 
                f -> (e_f)_R)
            )
        );
    R/I         
    )

brokenCircuitComplex = method (TypicalValue => SimplicialComplex)
brokenCircuitComplex (OrderedMatroid, Ring) := (M, R) -> (
    x := getSymbol "x";
    S := R[apply(M.orderedGround, e -> (getSymbol "x")_e), 
            Weights => toList(0..<#M.orderedGround)]; 
    brokenCircuits := apply(M.orderedCircuits, C -> delete(first C, C));
    I := monomialIdeal apply(
        brokenCircuits, 
        C -> product apply(C, e -> (value "x")_e));
    simplicialComplex I
    )
brokenCircuitComplex OrderedMatroid := M -> (
    brokenCircuitComplex (M, ZZ/1999))

matroidCharacteristicPolynomial = method(TypicalValue => RingElement)
matroidCharacteristicPolynomial OrderedMatroid := RingElement => M -> (
    hilb := numerator reduceHilbert hilbertSeries matroidOrlikSolomon M;
    d := (degree hilb)#0;
    --R := newRing (ring hilb, Inverses => true, MonomialOrder => Lex);
    --hilb := sub (hilb, R);
    R := ring hilb;
    use R;
    T := R_0;
    T^d* sub(hilb, T => -1 * T^-1)
    )   
matroidCharacteristicPolynomial Matroid := RingElement => M -> (
    matroidCharacteristicPolynomial orderedMatroid M)

-- TEX ACTIVE ORDERS
-- first we get a nice layout for the internal order
texInternalOrder = method(Options => {symbol Jitter => false})
texInternalOrder Poset := String => opts -> P -> print (
    --if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
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
    "\n\\tikzstyle{every node} = [draw = black, fill = white, rectangle, inner sep = 1pt]\n\\begin{tikzpicture}[scale = 1]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list {
        "    \\node (", toString F_i_j,") at (-",toString halflevelsets_i,"+",toString(0 + spacings_i_j),",",toString(scaleh*i),")",
            "    {\\scriptsize${",
            concatenate(
                concatenate ("{",listToTexString  ((P.GroundSet_(F_i_j))#0),"}"), 
                concatenate ("^{",listToTexString ((P.GroundSet_(F_i_j))#1),"}"), 
                concatenate ("_{",listToTexString ((P.GroundSet_(F_i_j))#2),"}")
                ),
            "}$}",
            ";\n"}
            ,
    concatenate(
        "  \\foreach \\to/\\from in ", 
        toString edgelist, 
        "\n  \\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )
    )

-- Next we get a nice layout for the external order
texExternalOrder = method(
    Options => {symbol Jitter => false})
texExternalOrder Poset := String => opts -> P -> print (
    --if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
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
    if class((P.GroundSet)#0#0) === List then
    -- The TeX String showing externally active elements as superscripts
    "\n\\tikzstyle{every node} = [draw = black, fill = white, rectangle, inner sep = 1pt]\n\\begin{tikzpicture}[scale = 1]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list {
        "    \\node (", toString F_i_j,") at (-",toString halflevelsets_i,"+",toString(0 + spacings_i_j),",",toString(scaleh*i),")",
            "    {\\scriptsize${",
            concatenate(
                concatenate ("{",listToTexString  ((P.GroundSet_(F_i_j))#0),"}"), 
                concatenate ("^{",listToTexString ((P.GroundSet_(F_i_j))#1),"}")
                ),
            "}$}",
            ";\n"}
            ,
    concatenate(
        "  \\foreach \\to/\\from in ", 
        toString edgelist, 
        "\n  \\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )
    else
    -- The TeX String without externally active elements as superscripts
    "\n\\tikzstyle{every node} = [draw = black, fill = white, rectangle, inner sep = 1pt]\n\\begin{tikzpicture}[scale = 1]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list {
        "    \\node (", toString F_i_j,") at (-",toString halflevelsets_i,"+",toString(0 + spacings_i_j),",",toString(scaleh*i),")",
            "    {\\scriptsize${",
            concatenate(
                concatenate ("{",listToTexString  ((P.GroundSet_(F_i_j))),"}"), 
                ),
            "}$}",
            ";\n"}
            ,
    concatenate(
        "  \\foreach \\to/\\from in ", 
        toString edgelist, 
        "\n  \\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )
    )    

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
            @TO "MatroidActivities"@ facilitates computations with @TO2 
            {matroid, "matroids"}@ and @TO2 {OrderedMatroid, "ordered 
            matroids"}@. It is an extension of the @TO Matroids@ package and 
            should eventually be subsumed by it. This package defines the new 
            class @TO2 {OrderedMatroid, "OrderedMatroid"}@. Just as in the @TO 
            Matroids@ package, one can make an @TO2 {orderedMatroid, "ordered 
            matroid"}@ from a @TO2 {matrix, "matrix"}@ or from a @TO2 {graph, 
            "simple graph"}@. In addition, this package makes it possible to 
            construct (ordered) matroids from @TO2 {CentralArrangement, 
            "central hyperplane arrangements"}@ over fields or ZZ, as well as 
            from @TO2 {SimplicialComplexes, "simplicial complexes"}@ and @TO2 
            {MonomialIdeal, "monomial ideals"}@.

            @TO MatroidActivities@ was initially created to compute general 
            matroid activities defined by Las Vergnas in [LV01]. (This is also 
            what inspired the name of the package.) In order to make these 
            computations we introduce the new type @TO OrderedMatroid@ 
            consisting of a @TO2 {matroid,"matroid"}@ together with a linear 
            order on the ground set of the matroid. In addition to methods for 
            computing @TO2 {internallyActiveElements, "internal"}@ and @TO2 
            {externallyActiveElements, "external activities"}@ of arbitrary 
            subsets of the ground set of an ordered matroid, one can also 
            compute the @TO2 {internalOrder, "internal"}@ and @TO2 
            {externalOrder, "external orders"}@ of an ordered matroid. In 
            particular, one can test if an ordered matroid is @TO2 
            {isInternallyPerfect, "internally perfect"}@ as defined in [Da15]. 
            There is also a method for computing the @TO2 {bjornersPartition, 
            "Bjorner partition"}@ of the boolean lattice (see [Bj92]) induced 
            by a given linear ordering of the ground set.

            In addition to the combinatorial methods described above, @TO 
            MatroidActivities@ also allows one to compute a number of  
            algebro-geometric structures associated to a (not necessarily 
            ordered) matroid M: the @TO2 {matroidIndependenceComplex, 
            "independence complex"}@ of M and its @TO2 {faceIdeal, "face 
            ideal"}@ [St83]; the @TO2 {brokenCircuitComplex,"broken circuit 
            complex"}@ of M and its @TO2 {faceIdeal, "face ideal"}@ (see e.g. 
            [BZ91]); the @TO2 {matroidChowRing,"Chow ring"}@ of M [AKM15]; and 
            the @TO2 {matroidOrlikSolomon,"Orlik-Solomon algebra"}@ of M 
            [OS80].

            @BR{}@ @BR{}@
            {\bf Setup}

            This package uses (and should evenutally be subsumed by) the 
            package @TO Matroids@, so install this first. The source code for 
            the Matroids package can be found @HREF{ "https://github.com/
            jchen419/Matroids-M2", "here"}@.

            Once the Matroids package is installed place the source file for 
            this package (available @HREF{"https://github.com/ aarondall/
            MatroidActivities-M2/blob/master/MatroidActivities.m2", "here"}@) 
            somewhere into the M2 @TO2 {"path", "search path"}@ and install 
            the package by calling @TO installPackage@ (MatroidActivities).

            {\bf References}@BR{}@

            @UL{
                "[AKH15] Hodge Theory for Combinatorial Geometries  (
                K. Adiprasito, J. Huh, and E. Katz, 2015)",
                "[Bj92] Homology and shellability of matroids and 
                geometric lattices, (A. Bjorner, 2001)", 
                "[BZ91] Broken Circuit Complexes: Factorizations and 
                Generalizations, (A. Bjorner and G. Ziegler, 1991)",
                "[Da15] Internally Perfect Matroids, (A. Dall, 
                2015)",
                "[LV01] Active Orders for Matroid Bases,  (M. Las 
                Vergnas, 2001)",
                "[OS80] Combinatorics and Topology of Complements of 
                Hyperplanes (P. Orlik and L. Solomon, 1980)",
                "[St83] Combinatorics and Commutative Algebra (
                Stanley, 1983)"
                }@
    SeeAlso
        Depth
        HyperplaneArrangements
        Matroids
        Posets
        SimplicialComplexes
///

doc ///
    Key
        OrderedMatroid
    Headline
        the class of ordered matroids
    Description
        Text
            An @TO2 {orderedMatroid, "ordered matroid"}@ is a @TO matroid@ 
            together with a linear order on its @TO2{ground, "ground set"}@. 
            In this package an ordered matroid is stored as a @TO2 
            {hashTable,"hash table"}@ with the following @TO keys@:  @TO 
            orderedGround@, @TO orderedBases@, @TO orderedCircuits@, @TO 
            orderedCocircuits@, and @TO Presentations@. There is also a @TO2 
            {cache, "cache"}@ available for storing computed data.
        Example
            peek orderedMatroid uniformMatroid(2,4) 
        Text    
            The list @TO orderedGround@ induces the linear order on the ground 
            set given by $e_i < e_j$ if $i$ precedes $j$ in the list. The list 
            @TO orderedBases@ (respectively, @TO orderedCircuits@, @TO 
            orderedCocircuits@) is the lex-ordering (with respect to 
            @TO orderedGround@) of the @TO bases@ (respectively, @TO 
            circuits@, cocircuits) of M, each ordered with respect to @TO 
            orderedGround@.

            We now construct three (unordered) graphic matroids we will use as 
            examples throughout the documentation of this package: MKn is the 
            cycle matroid of the @TO2 {completeGraph ,"complete graph"}@ on 
            n vertices and MG is MK4 with one element @TO2 {deletion, 
            "deleted"}@.
        Example
            K3 = completeGraph 3;
            MK3 = matroid K3;
            K4 = completeGraph 4;
            MK4 = matroid K4;
            G = deleteEdges (K4,{{2,3}});
            MG = matroid G;
        Text
            To make a matroid into an ordered matroid one provides
            a list that is used to linearly order the ground set.
            Alternatively, if no list is given the natural order
            on the ground set is taken.
        Example
            OM = orderedMatroid (MK3, {2,1,0});
            peek OM
            peek orderedMatroid MK3 
        Text
            The method @TO2 {orderedMatroid, "orderedMatroid"}@ can take many 
            arguments other than matroids. For example, one can create an 
            ordered matroid directly from a graph.
        Example
            OM1 = orderedMatroid K3 -- ordered matroid defined from a graph
        Text
            The original data from which an ordered matroid is made can always 
            be retrieved. There are two cases for how this is achieved 
            depending on whether the ordered matroid was defined from a(n 
            unordered) matroid or not.
        Example
            OM.matroid -- returns the underlying unordered matroid of OM
            OM1.Presentations.Graph -- returns the underlying graph of OM1
    Caveat
            The method @TO matroid@ does not check that the result is in fact 
            a matroid and @TO2 {orderedMatroid, "orderedMatroid"}@ inherits 
            this property. To check that the ordered bases of an ordered 
            matroid satisfy the basis exchange axiom we use @TO isValid@ on 
            the key "matroid".
    SeeAlso
        completeGraph
        deletion
        matroid
        orderedMatroid
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
            Shortens the default output for an object of type OrderedMatroid.
        Example
            MK3 = orderedMatroid completeGraph 3
            net MK3
///

doc ///
    Key
        orderedMatroid
        (orderedMatroid, CentralArrangement)
        (orderedMatroid, CentralArrangement, List)
        (orderedMatroid, Graph)
        (orderedMatroid, Graph, List)
        (orderedMatroid, Ideal)
        (orderedMatroid, Ideal, List)
        (orderedMatroid, Matrix)
        (orderedMatroid, Matrix, List)
        (orderedMatroid, Matroid)
        (orderedMatroid, Matroid, List)
        (orderedMatroid, SimplicialComplex)
        (orderedMatroid, SimplicialComplex, List)

    Headline
        construct an ordered matroid
    Usage
        OM = orderedMatroid(X, L)
        OM = orderedMatroid(X)
    Inputs
        X:Thing
            either a @TO CentralArrangement@, @TO Graph@, @TO Ideal@, @TO 
            Matrix@, @TO Matroid@, or an @TO SimplicialComplex@
        L:List
    Outputs
        OM:OrderedMatroid
    Description
        Text
            An ordered matroid is a @TO matroid@ M on a ground set E together 
            with a linear ordering on E. Given an ordered matroid, the linear 
            order induces a linear order on every subset of E as well as a 
            graded lexicographic ordering (graded by cardinality) on the set 
            2^E of all subsets of E.

            The method @TO orderedMatroid@ permits the user to construct 
            ordered matroids from a variety of structures defined across many 
            packages of Macaulay2. Since every ordered matroid contains a 
            matroid as part of its data one can, in particular, produce 
            unordered matroids for instances of each of these structures.

            First we construct an ordered matroid from a @TO Matroid@ object M 
            and a list L. The list L orders the (indices of the) ground set E 
            of M as follows:@BR{}@
            @BR{}@
                (1) the elements of E that appear in L appear first and in the 
                same order as they appear in L; @BR{}@
                (2) the elements of E not in L appear after all that do and 
                are ordered with respect to the natural ordering on E.@BR{}@
                @BR{}@
            In particular L need not be a permutation of E, nor even a subset.
            
            The next example illustrates these ideas by giving three lists 
            that yield the same ordered matroid of MK3, the cycle matroid of 
            the complete graph on 3 vertices.
        Example
            MK3 = matroid completeGraph 3;
            peek orderedMatroid(MK3, {2,0,1}) -- use a permutation of the ground set
            peek orderedMatroid(MK3, {2}) -- use a sublist of {2,0,1}
            peek orderedMatroid(MK3, {15/3, 2, .3, "a"}) --an arbitrary list in which 2 is the first element of the ground set to appear   
        Text
            It is often desirous to view a given matroid as an ordered matroid 
            with the natural ordering on the ground set. In this case one can 
            omit the list from the input data.
        Example
            orderedMatroid MK3 == orderedMatroid (MK3,{})
        Text
            One can also apply the method @TO2 {orderedMatroid, 
            "orderedMatroid"}@ to any of the following types just as is done 
            for matroids: @TO CentralArrangement@, @TO Graph@, @TO 
            SimplicialComplex@, @TO Ideal@, and @TO Matrix@,. To illustrate we 
            produce the ordered matroid of MK3 with the ordering 2 < 0 < 1 in 
            a number of different ways.
            
            For a central hyperplane arrangement, one obtains the vector 
            matroid on the matrix of normal vectors appropriately ordered by 
            L. The arrangement is stored in the @TO Presentations@ cache.
        Example 
            OM = orderedMatroid(MK3, {2,0,1});
            OM1 = orderedMatroid (typeA (2), {2,0,1});
            peek OM1
            peek OM1.Presentations
            representationOf OM1.matroid == sub(coefficients typeA 2, QQ)
            OM == OM1
        Text
            For a graph, the cycle matroid on the (ordered) edges is produced and the graph is stored.
        Example     
            OM2 = orderedMatroid (completeGraph 3, {2,0,1});
            peek OM2
            peek OM2.Presentations
            peek OM2.cache
        Text
            The ordered matroids OM1 and OM2 are @TO2 {(symbol ==, 
            OrderedMatroid, OrderedMatroid), "equal"}@. Note that ordered matroid equality is @ITALIC "different"@ from matroid equality.
        Example
            OM1 == OM2
        Text
            For a simplicial complex C, @TO orderedMatroid@ tests if the complex is the @TO2 {matroidIndependenceComplex, "independence complex"}@ of some matroid by first testing if C is @TO2 {isPure, "pure"}@ (a necessary condition) and then checking whether the @TO facets@ of C satisfy the @TO2 {isValid, "basis exchange axiom"}@. In case C does not satisfy one of these properties, an error is thrown indicating which.
        Example
            R = QQ[a..c];
            OM3 = orderedMatroid (simplicialComplex {a*b, b*c, c*a}, {2,0,1});
            peek OM3
            peek OM3.Presentations
            OM2 == OM3
        Text
            For an ideal, @TO orderedMatroid@ checks if the ideal is the @TO2 
            {faceIdeal, "face ideal"}@ of the @TO2 
            {matroidIndependenceComplex, "independence complex"}@ of some 
            matroid. (As the face ideal of the independence complex of a 
            matroid is generated by the @TO circuits@ of the matroid, we refer 
            to it as the circuit ideal.) In particular, the ideal must be a 
            @TO2 {isSquareFree, "square-free"}@ @TO2 {MonomialIdeal, "monomial 
            ideal"}@ such that the corresponding @TO2 {SimplicialComplex, 
            "simplicial complex"}@ satisfies the conditions above. 
        Example
            I = monomialIdeal "abc";
            OM4 = orderedMatroid (I, {2,0,1});
            peek OM4
            OM3 == OM4
            OM4.Presentations.CircuitIdeal ==
             OM3.Presentations.IndependenceComplex.faceIdeal
        Text
            As noted above there are four ways that applying @TO 
            orderedMatroid@ to an arbitrary ideal I can fail to output an 
            ordered matroid. In any of these four cases an error will be 
            thrown giving the reason for the failure. When I is not of the 
            class @TO MonomialIdeal@ or when I is not @TO2 {isSquareFree, 
            "square-free"}@ the error message will also give hints about how 
            to approximate I so as to try to make an ordered matroid that may 
            be somewhat useful in studying the original ideal.

            Finally we turn our attention from ideals to matrices.
            For a matrix, one obtains the vector matroid on the columns,  
            ordered with respect to L. 
        Example
            OM5 = orderedMatroid (matrix {{1,0,1},{0,1,1}}, {2,0,1});
            peek OM5
            peek OM5.Presentations
            OM5 == OM4
        Text
            Since an ordered matroid is a type of @TO2 {HashTable, "hash 
            table"}@, it consists of a pairs of the form @TO keys@ => @TO 
            values@. One accesses a @TO2 {value,"value"}@ of an ordered 
            matroid as follows. 
        Example
            OM5.cache
            OM5.matroid
            OM5.orderedBases
            OM5.orderedCircuits
            OM5.orderedCocircuits
            OM5.orderedGround   
            OM5.Presentations
        Text
            As we have seen in previous examples, we can access the @TO2 
            {Presentations, "presentations"}@ and cache of an ordered matroid 
            in a similar manner.
        Example
            OM5.cache.isRepresentableMatroid
            OM5.Presentations.Matrix    
    SeeAlso
        (symbol ==, OrderedMatroid, OrderedMatroid)
        arrangement
        graph
        isCentral
        matrix
        orderedBases
        orderedCircuits
        orderedCocircuits
        orderedGround
        orderedMatroid
        OrderedMatroid
///

doc ///
    Key
        CircuitIdeal
    Headline
        the face ideal of the independence complex of a matroid
    Usage
        M.cache.CircuitIdeal
        OM.Presentations.CircuitIdeal
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        I:Ideal
    Description
        Text
            For a @TO2 {Matroid, "matroid"}@ M, the @TO2 {faceIdeal, "face 
            ideal"}@ of the @TO2 {matroidIndependenceComplex, "independence 
            complex"}@ of M. 
        Example
            MK3 = matroid completeGraph 3;
            peek MK3.cache
            matroidIndependenceComplex MK3;
            peek MK3.cache
        Text
            For a @TO2 {Matroid, "matroid"}@ M, the @TO2 {faceIdeal, "face 
            ideal"}@ of the @TO2 {matroidIndependenceComplex, "independence 
            complex"}@ of M over a polynomial ring with the lex-order induced 
            by the ordering on the @TO2 {orderedGround, "ordered ground set"}@ 
            of M.
        Example
            OMK3 = orderedMatroid (completeGraph 3, {2, 1, 0});
            peek OMK3.cache
            matroidIndependenceComplex OMK3;
            peek OMK3.cache 
    SeeAlso
        matroidIndependenceComplex
        faceIdeal
        isMatroidIndependenceComplex
        matroidFVector
        matroidHPolynomial
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
            Two @TO2{orderedMatroid, "ordered matroids"}@ are declared equal 
            if their underlying unordered matroids are @TO isomorphic@ and if 
            their @TO2 {orderedGround, "ordered ground sets"}@ differ by a 
            permutation that acts only on @TO2 {parallelClasses, "parallel 
            classes"}@ of the underlying matroid.

            We illustrate using a matrix whose first and last 
            columns are parallel.
        Example
            m = sub(matrix {{1,0,1,2},{0,1,1,0}},QQ)
            parallelClasses matroid m
        Text
            Interchanging the two parallel elements does not effect
            the ordered matroid.
        Example     
            M = orderedMatroid (m,{});
            M1 = orderedMatroid (m,{3,1,2,0});
            M == M1
        Text
            Note that the method gives two data: first it prints 
            that the two underlying unordered matroids are equal 
            (that is, strongly  @TO2 {isomorphic,"isomorphic"}@) 
            and then it outputs whether the two ordered matroids 
            are equal.

            As the next example shows, it is possible for two 
            ordered matroids to have strongly isomorphic underlying 
            matroids even though they are not equal as ordered 
            matroids.
        Example 
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
            (orderedMatroid completeGraph 3).orderedGround
            (orderedMatroid (completeGraph 3, {2,1})).orderedGround
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
            Each element of this list is a basis of the underlying unordered 
            matroid M.@TO matroid@ ordered with respect to the @TO2 
            {orderedGround, "ordered ground"}@ set of M. Moreover, the whole 
            list is ordered by the lexicographical order induced by the @TO2 
            {orderedGround, "ordering"}@ on the ground set.
        Example
            (orderedMatroid completeGraph 3).orderedBases
            (orderedMatroid (completeGraph 3, {2,1})).orderedBases
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
            Each @TO2 {orderedCircuits, "ordered circuit"}@ is a circuit of 
            the underlying unordered matroid that is ordered with respect to 
            the @TO2 {orderedGround, "ordered ground set"}@. Just as for @TO2 
            {orderedBases, "ordered bases"}@, the list of ordered circuits is 
            lexicographically ordered with respect to the @TO2 {orderedGround, 
            "ordered ground set"}@.
        Example
            MK3 = matroid completeGraph 3;
            (orderedMatroid completeGraph 3).orderedCircuits
            (orderedMatroid (completeGraph 3, {2,1})).orderedCircuits
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
            Each @TO2 {orderedCocircuits,"ordered cocircuit"}@ 
            is a circuit of the dual of the underlying unordered matroid that 
            is ordered with respect to the @TO2 {orderedGround, "ordered 
            ground set"}@. Just as for @TO2 {orderedBases, "ordered bases"}@, 
            the list of ordered cocircuits is lexicographically ordered with 
            respect to the @TO2 {orderedGround, "ordered ground set"}@.
        Example
            MK3 = orderedMatroid completeGraph 3;
            MK3.orderedCocircuits
            (orderedMatroid (MK3.matroid, {2,1})).orderedCocircuits
    SeeAlso
        orderedBases
        orderedCircuits
        orderedGround
        orderedMatroid
        OrderedMatroid
///

doc ///
    Key
        Presentations
    Headline
        cached presentations of an ordered matroid
    Usage
        M.Presentations
    Inputs
        M:OrderedMatroid
    Outputs
        :CacheTable
    Description
        Text
            An @TO2 {orderedMatroid, "ordered matroid"}@ may be presented in a 
            variety of ways. This cache table stores those presentations with 
            the exception of when an ordered matroid is presented as a @TO 
            matroid@ and a @TO2 {List, "list"}@. For example, when creating an 
            ordered matroid from a graph both the graph and the @TO2 
            {signedIncidenceMatrix, "signed incidence matrix"}@ of the graph 
            are stored.
        Example
            M = orderedMatroid completeGraph 3;
            peek M.Presentations
        Text
            As one works with an ordered matroid new presentations can be 
            added to @TO Presentations@. For example, when one computes the 
            @TO2 {matroidIndependenceComplex, "independence complex"}@ of an 
            ordered matroid both the complex and the @TO2 {CircuitIdeal, 
            "circuit ideal"}@ are stored.
        Example
            matroidIndependenceComplex M;
            peek M.Presentations        
    SeeAlso
        orderedMatroid
        matroidIndependenceComplex
///

doc ///
    Key
        orderedFlats
        (orderedFlats, OrderedMatroid)
    Headline
        the ordered flats of an ordered matroid
    Usage
        C = orderedFlats(OM)
    Inputs
        OM:OrderedMatroid
    Outputs
        F:List
            consisting of the ordered flats
    Description
        Text
            Applying this method to an ordered matroid returns the 
            @TO flats@ of the underlying matroid as lists that are ordered 
            with respect to the given linear ordering on the ground set.
            Note that the while each flat is ordered with respect to the
            ordering on the ground set, the lists of flats of each rank are 
            not.
        Example
            MK3 = matroid completeGraph 3;
            F1 = orderedFlats orderedMatroid (MK3, {2,0,1})
            F2 = orderedFlats orderedMatroid MK3
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
    Headline
        test if an element is active
    Usage
        isActive(OM,A,e)
    Inputs
        OM:OrderedMatroid
        A:List
            a list of indices of ground set elements
        e:ZZ
            an element of the ground set
    Outputs
        :Boolean
            whether e is active in OM with respect to A
    Description
        Text
            An element e of the ground set of an ordered matroid OM is active 
            with respect to a subset A of the ground set if there is an 
            @TO2{orderedCircuits, "ordered circuit"}@ C of OM such that C is 
            contained in A $\cup$ e and e is the smallest element of $C$ with 
            respect to the linear order on the ground set.
        Example
            MK3 = orderedMatroid completeGraph 3
            MK3.orderedCircuits
            isActive (MK3, {1,2}, 0)
        Text    
            The property of being active depends on the given order of the 
            ground set. Continuing with the above example, we change the order 
            on the ground set and see that 0 is no longer active with respect 
            to \{1,2\}.
        Example
            OM = orderedMatroid (MK3.matroid, {2,0,1}); -- changing the order
            isActive (OM, {1,2}, 0) -- may effect activity
    Caveat
        Many of the routines in this package use @TO isActive@ or @TO 
        isDuallyActive@ as a subroutine, and therefore depend on the given 
        linear order @TO2 {orderedGround, "ordered ground"}@.
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
    Headline
        test if an element is active in the dual
    Usage
        isDuallyActive(OM,A,e)
    Inputs
        OM:OrderedMatroid
        A:List
            a list of indices of ground set elements
        e:ZZ
            an element of the ground set
    Outputs
        :Boolean
            whether e is active in the ordered dual of OM with respect to A
    Description
        Text
            An element e of the @TO2{orderedGround, "ground set"}@ of an 
            ordered matroid OM is active in the dual of OM with respect to a 
            subset A of the ground set if there is an ordered cocircuit C$^*$ 
            of OM such that C$^*$ is contained in A $\cup$ e and e is the 
            smallest element of C$^*$ with respect to the linear order on the 
            ground set, @TO2 {orderedGround, "ordered ground"}@.
        Example
            MK3 = orderedMatroid completeGraph 3;
            MK3.orderedCocircuits
            isDuallyActive (MK3, {0,1}, 0)
        Text        
            The property of being dually active depends on the given order of 
            the ground set. Continuing with the above example, we change the 
            order on the ground set and see that 0 is no longer active with 
            respect to \{0,1\}.
        Example
            OM = orderedMatroid (MK3.matroid, {2,1,0})
            isDuallyActive (OM, {0,1}, 0)
    Caveat
        Many of the routines in this package use @TO isActive@ or @TO 
        isDuallyActive@ as a subroutine, and therefore depend on the given 
        linear order @TO2 {orderedGround, "ordered ground"}@.
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
    Headline
        the active elements with respect to a subset
    Usage
        Act = activeElements(OM,A)
    Inputs
        OM:OrderedMatroid
        A:List
            of indices of ground set elements
    Outputs
        Act:List
            consisting of the active elements of the ground set of an ordered 
            matroid with respect to the elements of A
    Description
        Text
            For an ordered matroid the @TO2 {isActive, "active elements"}@ 
            with respect to the elements in A are computed with respect to the 
            given linear order of the ground set and returned as a list 
            ordered with respect to the @TO2 {orderedGround, "ordered ground 
            set"}@.
        Example
            MK3 = orderedMatroid completeGraph 3
            Act = activeElements (MK3, {0,1})
        Text
            In general, varying the order varies the active elements. For 
            example, taking a different ordering on the ground set of MK3
            changes the active elements of \{0,1\}.
        Example
            OM = orderedMatroid (MK3.matroid, {2,0,1})
            Act1 = activeElements (OM, {0,1})
///

doc ///
    Key
        duallyActiveElements
        (duallyActiveElements, OrderedMatroid, List)
    Headline
        the active elements with respect to a subset
    Usage
        Act = duallyActiveElements(OM,A)
    Inputs
        OM:OrderedMatroid
        A:List
            of indices of ground set elements
    Outputs
        Act:List
            consisting of the active elements of the ground set of the dual of 
            an ordered matroid with respect to the elements of A
    Description
        Text
            For an ordered matroid, the active elements of the @TO2 
            {dualMatroid,"dual matroid"}@ with respect to the set A are 
            computed with respect to the @TO2 {orderedGround,"ordered ground 
            set"}@ and returned as an ordered list.
        Example
            MK3 = matroid completeGraph 3;
            OM = orderedMatroid (MK3, {2,0,1});
            Act = duallyActiveElements(OM, {0,1})
        Text
            As with @TO activeElements@, changing the order on the ground set 
            can change the dually active elements of a set.
        Example
            OM1 = orderedMatroid (MK3, {0,1,2});
            Act1 = duallyActiveElements (OM1, {0,1})
    SeeAlso
        externallyActiveElements
        internallyActiveElements        
///

doc ///
    Key
        externallyActiveElements
        (externallyActiveElements, OrderedMatroid, List)
    Headline
        the externally active elements of a subset of the ground set
    Usage
        EA = externallyActiveElements(OM,A)
    Inputs
        OM:OrderedMatroid
        A:List
            consisting of indices of ground set elements
    Outputs
        EA:List
            the externally active elements of OM with respect to A
    Description
        Text
            Given an ordered matroid and a subset A of the @TO2 
            {orderedGround,"ordered ground set"}@, an element e of the ground 
            set is externally active with respect to A if e is active with 
            respect to A and e is not an element of A.

            For the cycle matroid MK3 of the complete graph on three vertices 
            with the natural order, we see that then there are no externally 
            active elements with respect to the set consisting of 0 and 1.
        Example
            MK3 = orderedMatroid completeGraph 3;
            EA = externallyActiveElements (MK3, {0,1})
        Text
            On the other hand, if the linear order on MK3 is given by 2 < 0 < 
            1, then e = 2 is the only externally active element.
        Example
            OM = orderedMatroid (MK3.matroid, {2,0,1});
            EA = externallyActiveElements (OM, {0,1})
    SeeAlso
        isActive
        orderedMatroid
        externalOrder
        externallyPassiveElements
///

doc ///
    Key
        externallyPassiveElements
        (externallyPassiveElements, OrderedMatroid, List)
    Headline
        the externally passive elements of a set
    Usage
        EP = externallyPassiveElements(OM,A)
    Inputs
        OM:OrderedMatroid
        A:List
            consisting of indices of ground set elements
    Outputs
        EA:List
            consisting of the externally passive elements of an ordered 
            matroid with respect to A
    Description
        Text
            Given an ordered matroid, an element e of the ground set is 
            externally passive with respect to the set A if it is not in A and 
            it is not externally active with respect to A.

            For the cycle matroid MK3 of the complete graph on three vertices 
            with the natural order, we see that e = 2 is externally passive 
            with respect to the set consisting of 0 and 1.
        Example
            MK3 = orderedMatroid completeGraph 3;
            EP = externallyPassiveElements(MK3, {0,1})
        Text
            On the other hand, if the linear order on MK3 is given by 2 < 0 < 
            1 then there are no externally passive elements.
        Example
            OM = orderedMatroid(MK3.matroid,{2});
            EP = externallyPassiveElements(OM, {0,1})
    SeeAlso
        orderedMatroid
        isActive
        externallyActiveElements
        externalOrder
///

doc ///
    Key
        internallyActiveElements
        (internallyActiveElements, OrderedMatroid, List)
    Headline
        the internally active elements of a set
    Usage
        IA = internallyActiveElements(OM,A)
    Inputs
        OM:OrderedMatroid
        A:List
            consisting of elements of the ground set
    Outputs
        IA:List
            consisting of internally active elements of A
    Description
        Text
            For an ordered matroid OM with @TO2 {orderedGround,"ordered ground 
            set"}@ E, an element e of E is internally active with respect to a 
            subset A of the ground set if e is in A and there is an ordered 
            cocircuit C$^*$ of OM such that (1) C$^*$ is contained in E-A \cup 
            e and (2) e is the least element of C$^*$.
        Example
            MK3 = orderedMatroid completeGraph 3;
            MK3.orderedCocircuits
            IA1 = internallyActiveElements (MK3, {0,1}) 
        Text    
            Internal activity depends on the order of the ground set.
        Example
            OM = orderedMatroid (MK3.matroid, {2,0,1});
            OM.orderedCocircuits
            IA2 = internallyActiveElements (OM, {0,1})
        Text
            By matroid duality we have that an element e is internally active 
            with respect to A if and only if e is externally passive with 
            respect to E-A.
        Example
            EP1 = externallyPassiveElements(MK3, {2});
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
    Headline
        the internally passive elements of a set
    Usage
        IA = internallyPassiveElements(OM,A)
    Inputs
        OM:OrderedMatroid
        A:List
            consisting of elements of E
    Outputs
        IA:List
            consisting of internally passive elements of A
    Description
        Text
            Given an ordered matroid, an element e of the @TO2 
            {orderedGround,"ordered ground set"}@ is internally passive with 
            respect to the set A if e is not @TO2 
            {internallyActiveElements,"internally active"}@ with respect to A.
        Example
            MK3 = orderedMatroid completeGraph 3;
            IA = internallyPassiveElements(MK3, {0,1})
        Text
            Internal passivity depends on the order of the ground set.
        Example
            OM = orderedMatroid (MK3.matroid, {2,0,1})
            IA1 = internallyPassiveElements (OM, {0,1})
    SeeAlso
        isActive
        internallyActiveElements
        orderedMatroid
        internalOrder
///

doc ///
    Key
        externalOrder
        ShowExt
        (externalOrder, OrderedMatroid)
        [externalOrder, ShowExt]
    Headline
        the external order of an ordered matroid
    Usage
        P = externalOrder(OM)
    Inputs
        OM:OrderedMatroid
        ShowExt=>Boolean
            whether to include the externally active elements in the output
    Outputs
        P:Poset
            the external order of an ordered matroid
    Description
        Text
            The external order of an ordered matroid OM is the poset
            on the @TO2{orderedBases},"ordered bases"@ of OM defined by the 
            relation b1 < b2 if b1 is a subset of the union of b2 and the 
            @TO2{externallyActiveElements,"externally active elements"}@ of b2.
            (See [LV01] for equivalent conditions.)

            The @TO ShowExt@ option enables the user to modify the ground set 
            of the poset. The default setting (ShowExt => false) outputs the 
            external order as defined above. 
        Example
            MK3 = orderedMatroid completeGraph 3;
            P = externalOrder MK3
            P.GroundSet
        Text
            Setting ShowExt => true outputs an isomorphic poset whose labels 
            consist of pairs \{B, Ext(B)\} where B is a basis and Ext(B) is 
            the set of @TO2 {externallyActiveElements,"externally active 
            elements"}@ of B. We illustrate the difference in the next example.
        Example
            Q = externalOrder (MK3, ShowExt => true);
            Q.GroundSet
        Text
            For some examples the external order is an invariant of the 
            underlying unordered @TO matroid@, that is, it is independent of 
            the linear order on the ground set of the matroid. Let us 
            illustrate this with the three cycle.
        Example
            isomorphismClasses = removeIsomorphicPosets (
                apply(permutations 3, p -> externalOrder orderedMatroid (MK3.matroid,p)))
        Text
            In general, however, the isomorphism class of the external order 
            can vary with the given linear order. We illustrate this for the 
            cycle matroid MG of the graph obtained from the complete graph on 
            four vertices by removing one edge. We find that there are exactly 
            two isomorphism classes among the 5! possible permutations.
        Example
            MK4 = orderedMatroid (completeGraph 4);
            MG = orderedMatroid (deletion_(MK4.matroid) {5});
            isomorphismClasses = removeIsomorphicPosets (
                apply(permutations 5, p -> externalOrder orderedMatroid(MG.matroid,p))
                );
            tally oo    
        Text
            In [LV01], it is shown that the external order is a @TO2 
            {isGraded,"graded poset"}@ and that it becomes a graded @TO2{ 
            isLattice, "lattice"}@ once an artificial bottom element is added. 
            We confirm these facts for the two isomorphism classes of external 
            orders of the matroid MG.
        Example
            tally apply (isomorphismClasses, P -> isGraded P)
            tally apply (isomorphismClasses, P -> isLattice (adjoinMin P))
        Text
            Though the external order of an ordered matroid is not, in 
            general, an invariant of the underlying matroid, its @TO2 
            {rankGeneratingFunction, "rank generating function"}@ is. More 
            precisely, for any linear ordering of the ground set of an 
            unordered matroid M, the rank generating function of the @TO2 
            {dual, "dual poset"}@ of the induced external order is the @TO2 
            {matroidHPolynomial, "matroid h-polynomial"}@ of the @TO2 
            {dualMatroid, "dual matroid"}@. Let us verify this for the matroid 
            MG. 
        Example
            apply(isomorphismClasses, P -> rankGeneratingFunction dual P)
            matroidHPolynomial (dualMatroid MG.matroid)

        Text
            By matroid duality, the external order of an ordered matroid is 
            isomorphic to the poset dual of the @TO2 {internalOrder, "internal 
            order"}@ of the @TO2 {dualMatroid, "dual matroid"}@ (using the 
            same ordering on the ground set), as verified in the following 
            example.
        Example
            areIsomorphic (
                externalOrder MG, 
                dual internalOrder (orderedMatroid dualMatroid MG.matroid))
        Text
            The are two ways to obtain TikZ renderings of an external order to 
            include in a LaTeX document. The first is to use the method @TO2 
            {texPoset,"texPoset"}@ included in the @TO Posets@ package.
        Example
            texPoset externalOrder MG
        Text
            While there are some posets that @TO texPoset@ renders nicely, the 
            active orders of ordered matroids are not among them. For this 
            reason we supply a modification of that code that produces 
            renderings that are, in our opinion, more aesthetically pleasing. 
            See more at @TO texExternalOrder@.
        Example
            texExternalOrder externalOrder MG   
        Text
            @BR{}@ @BR{}@
            {\bf References}@BR{}@

            @UL{
                "[LV01] Active Orders for Matroid Bases  (M. Las Vergnas,
                2001)",
                }@
    SeeAlso
        internalOrder
        removeIsomorphicPosets
        isGraded
        isLattice
        rankGeneratingFunction
        matroidHPolynomial
        dualMatroid
        texExternalOrder
        adjoinMin
///

doc ///
    Key
        internalOrder
        (internalOrder, OrderedMatroid)
    Headline
        the internal order of an ordered matroid
    Usage
        P = internalOrder(OM)
    Inputs
        OM:OrderedMatroid
    Outputs
        P:Poset
            the internal order of an ordered matroid
    Description
        Text
            For an ordered matroid OM, the internal order is the @TO poset@ on 
            the @TO2 {orderedBases, "ordered bases"}@ of OM such that B_1 < 
            B_2 if every @TO2{internallyPassiveElements, "internally passive 
            element"}@ of B_1 is also internally passive in B_2. For example, 
            the internal order of the cycle matroid MG of the graph obtained 
            from the @TO2 {completeGraph, "complete graph"}@ on four vertices 
            by @TO2 {deletion, "deleting"}@ one edge is given in the following 
            example.
        Example
            MK4 = orderedMatroid (completeGraph 4);
            MG = orderedMatroid (deletion_(MK4.matroid) {5});
            P = internalOrder MG
            P.GroundSet 
        Text
            Notice that the @TO2 {groundSet,"ground set"}@ of the internal 
            order consists of partitions of the bases of MG in their @TO2 
            {internalBasisDecomposition,"internal basis decompositions"}@.
        
            The duality between @TO2{internallyActiveElements, "internally
             active elements"}@ of a basis B and @TO2{externallyActiveElements,
            "externally active elements"}@ of the dual basis induces an @TO 
            isomorphism@ between the internal order of an ordered matroid and 
            the poset dual of the @TO2 {externalOrder, "external order"}@ of 
            the @TO2 {dualMatroid, "dual"}@ ordered matroid.
        Example
            dualMG = orderedMatroid (dualMatroid MG.matroid);
            areIsomorphic (P, dual externalOrder dualMG)
        Text
            The @TO2 {rankGeneratingFunction,"rank generating function"}@ of 
            the internal order of an ordered matroid gives the @TO2 
            {matroidHPolynomial,"h-polynomial"}@ of the @TO2 
            {matroidIndependenceComplex, "independence complex"}@ of the 
            matroid.
        Example
            RGF = rankGeneratingFunction internalOrder MG
            h = matroidHPolynomial MG
            R = ring h;
            h == sub(RGF,R)
        Text
            The internal order of an ordered matroid depends on 
            the ordering of the ground set. For example there are four 
            isomorphism classes of internal orders induced by reorderings of 
            MG.
        Example
            # removeIsomorphicPosets apply(
                permutations 5, 
                p -> internalOrder orderedMatroid(MG.matroid,p)
                )
        Text
            To produce a TikZ rendering of an internal order for use in a 
            LaTeX document, use the @TO texInternalOrder@ method.
        Example
            texInternalOrder internalOrder MG   
    SeeAlso
        externalOrder
        rankGeneratingFunction
        areIsomorphic
        Posets
        texInternalOrder
///

doc ///
    Key
        minimalBasis
        (minimalBasis, OrderedMatroid, List)
    Headline
        compute the lex-minimal basis containing an independent set
    Usage
        B = minimalBasis(OM, I)
    Inputs
        OM:OrderedMatroid
        I:List
            corresponding to an independent set of the matroid
    Outputs
        B:List
            the lexicographically least basis of an ordered matroid containing 
            the elements in I.
    Description
        Text
            Every independent set of a matroid is contained in at least one 
            basis. If the matroid is ordered, the @TO2 {minimalBasis, "minimal 
            basis"}@ is the unique lexicographically smallest such basis with 
            the respect to the order. This method returns the minimal basis if 
            I is independent and throws an error otherwise.
        Example
            MK3 = orderedMatroid completeGraph 3
            minimalBasis (MK3, {2})
            try minimalBasis (MK3, {0,1,2}) else print "not independent"
///

doc ///
    Key
        internalBasisDecomposition
        (internalBasisDecomposition, OrderedMatroid, List)
    Headline
        Internal Basis Decomposition
    Usage
        internalBasisDecomposition(OM,B)
    Inputs
        OM:OrderedMatroid 
        B:List
            a basis of an ordered matroid
    Outputs
        D:List
            a tripartition of B
    Description
        Text
            Let B_0 be the lexicographically least basis of an @TO2 
            {orderedMatroid, "ordered matroid"}@ and let B be any basis. Then 
            @TO internalBasisDecomposition@ returns the following partition of 
            B: @BR{}@ 
            (\#0) S is the set of  @TO2{internallyPassiveElements, "internally 
            passive elements"}@ of B @EM "not in"@ B_0,@BR{}@
            (\#1) T is the set of @TO2{internallyPassiveElements, "internally 
            passive elements"}@ of B that @EM "are in"@ B_0, and @BR{}@
            (\#2) A is the set of @TO2{internallyActiveElements, "internally 
            active elements"}@ of B (necessarily in B_0).
        Example
            MK4 = orderedMatroid completeGraph 4;
            internalBasisDecomposition (MK4, {2,3,5})
            OM2 = orderedMatroid (MK4.matroid, {5,4,3,2,1,0});
            internalBasisDecomposition (OM2, {2,3,5})
    Caveat
        The method does not check that B is a basis of the ordered matroid. 
        Applying this method to lists that are not bases will have unexpected 
        results.
    SeeAlso
        internalOrder   
///

doc ///
    Key
        basisType
        (basisType, OrderedMatroid, List)
    Headline
        compute the type of a basis
    Usage
        basisType(OM, B)
    Inputs
        OM:OrderedMatroid
        B:List
            a basis of the ordered matroid
    Outputs
        :String
            either "perfect" or "abundant" or "deficient"
    Description
        Text
            Write S, T, and A for the three lists obtained from the @TO2 
            {internalBasisDecomposition, "internal basis decomposition"}@ of 
            the basis B. If S has a single element f, then B is called an 
            f-principal basis. For f in S let B(f) be the @TO2 {minimalBasis, 
            "minimal basis"}@ of T $\cup$ f and let T(f) be the elements of T 
            that are also @TO2 {internallyPassiveElements, "internally passive 
            elements"}@ of B(f). Then B is defined to be (internally) perfect 
            if the sets T(f) form a partition of T. Equivalently, there is 
            exactly one way to write B as the join of f-principal bases in the 
            internal order of OM.

            If the union of all the T(f) equals T but is not a disjoint union, 
            then B is called (internally) abundant. Equivalently, there is 
            more than one way to write B as the join of f-principal bases.

            Finally, B is (internally) deficient if it is neither perfect nor 
            abundant in which case there is no way to write B as the join of 
            f-principal bases.

            Note that if T is empty or S is a singleton, then B is trivially 
            perfect. For example, we compute the @TO2 
            {internalBasisDecomposition, "internal basis decomposition"}@ and 
            @TO2 {basisType, "basis type"}@ of two bases of the complete graph 
            on four vertices with the natural order on the ground set.
        Example
            MK4 = orderedMatroid completeGraph 4;
            (internalBasisDecomposition (MK4, {1,2,3}), basisType (MK4, {1,2,3}))
            (internalBasisDecomposition (MK4, {0,3,5}), basisType (MK4, {0,3,5}))
        Text
            The ordered matroid MK4 does have a deficient basis, and an 
            abundant one.
        Example
            basisType (MK4, {1,4,5})
            basisType (MK4, {2,4,5})
    Caveat
        As usual, the @TO2 {basisType, "basis type"}@ of a basis of an ordered 
        matroid will generally depend on the @TO2 {orderedGround, "ordered 
        ground set"}@.
    SeeAlso
        internalOrder
        isInternallyPerfect
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
        M:Matroid
    Outputs
        :Boolean
            whether a given (ordered) matroid is internally perfect
    Description
        Text
            An @TO2{orderedMatroid, "ordered matroid"}@ is internally perfect 
            if every basis is @TO2{basisType,"internally perfect"}@. By a 
            result in [Da15], the @TO2 {internalOrder, "internal order"}@ of 
            an internally perfect ordered matroid is @TO2 {areIsomorphic, 
            "isomorphic"}@ to a pure @TO2 {standardMonomialPoset, 
            "multicomplex"}@, and hence satisfies Stanley's conjecture on 
            matroid h-vectors.

            An unordered @TO matroid@ is said to be internally perfect if 
            there is some permutation of the ground set making it an 
            internally perfect ordered matroid.

            Some matroids are internally perfect for any ordering of the 
            ground set. Examples include the graphic matroid of any @TO2 
            {cycleGraph,"cycle"}@ on n vertices and any matroid of rank no 
            more than two.
        Example
            M = matroid cycleGraph 4;
            all (permutations 4, p -> isInternallyPerfect orderedMatroid (M,p))
        Text
            Some matroids are internally perfect for some orderings but not 
            for all. For example, consider the graphic matroid obtained from 
            removing one edge from the complete graph on four vertices.
        Example
            MK4 = orderedMatroid completeGraph 4;
            MG = orderedMatroid (deletion_(MK4.matroid) {5});
            isInternallyPerfect MG
            isInternallyPerfect orderedMatroid (MG.matroid,{1,2,0})
        Text
            Since the ordered matroid MG in the previous example is internally 
            perfect, its internal order is isomorphic to a pure multicomplex 
            (see [Da15]). We provide one multicomplex in the following example.
        Example
            P = internalOrder MG;
            R = ZZ[x,y] -- define a polynomial ring
            I = monomialIdeal (x^3, x*y^2, y^4) -- define a monomial ideal in R;
            Q = standardMonomialPoset I;
            isPure orderComplex Q
            areIsomorphic(P,Q)
        Text
            The poset Q in the above example is the pure multicomplex 
            consisting of all monomials that divide x^2y and y^3. These 
            monomials are obtained from the maximal elements of the internal 
            order P by writing each as the join of f-principal bases: 34^1 is 
            the join of 3^1_2 and 4_{01} while 4^{12} is a 4-principal basis.

            In contrast to the previous examples, there are matroids that are 
            not internally perfect for any ordering of the ground set. 
            Examples include the graphic matroid of the complete graph on 
            n > 3 vertices and any uniform matroid U(r,n) where 2 < r < n-1. 
            One can verify this by applying @TO isInternallyPerfect@ directly 
            to an unordered matroid.
        Example
            isInternallyPerfect matroid completeGraph 4
            isInternallyPerfect uniformMatroid(3,5)
        Text
            In particular, internally perfect matroids are not closed under 
            duality. For example, we saw in the previous example that the @TO2 
            {uniformMatroid, "uniform matroid"}@ U(3,5) is not internally 
            perfect. The dual matroid U(2,5) is a rank two matroid and so it 
            is internally perfect (for any ordering of its ground set).
        Example
            M := uniformMatroid (3,5);
            all (permutations 5, p -> isInternallyPerfect orderedMatroid(dualMatroid M, p))
        Text
            We can use @TO isInternallyPerfect@ to test if an unordered 
            matroid has a permutation of the ground set such that the 
            resulting ordered matroid is internally perfect. If it does, then 
            the method prints such an order. This test is computationally 
            expensive since r!b permutations (where r is the rank of the 
            matroid and b is the number of bases) need to be tested in the 
            case when the matroid is not internally perfect for any 
            permutation.
        Example
            isInternallyPerfect (MG.matroid)
            time isInternallyPerfect (MK4.matroid)  
        Text
            @BR{}@ @BR{}@
            {\bf References}@BR{}@
            
            @UL{
                "[Da15] Internally Perfect Matroids  (Dall,
                2015)",
                }@
    SeeAlso
        internalOrder
        orderComplex
        standardMonomialPoset
///

doc ///
    Key
        bjornersPartition
        (bjornersPartition, OrderedMatroid)
    Headline
        compute Bjorner's partition
    Usage
        bjornersPartition(OM)
    Inputs
        OM:OrderedMatroid
    Outputs
        :List
            consisting of pairwise disjoint closed intervals in the boolean 
            lattice on |E| elements
    Description
        Text
            For a basis B of an ordered matroid write EA(B) and IP(B) for the 
            @TO2 {externallyActiveElements, "externally active"}@ and @TO2 
            {internallyPassiveElements, "internally passive elements"}@ of B, 
            respectively. Bjorner proved that the intervals
            @BR{}@ @BR{}@
            [IP(B),B $\cup$ EA(B)]
            @BR{}@ @BR{}@
            in the @TO2 {booleanLattice, "boolean lattice"}@ on subsets of E 
            form a partition, which we call Bjorner's partition.
        Example
            MK3 = orderedMatroid completeGraph 3
            bjornersPartition MK3
///

doc ///
    Key
        latticeOfFlats
        Reduced
        (latticeOfFlats, Matroid)
        (latticeOfFlats, OrderedMatroid)
        [latticeOfFlats,Reduced]
    Headline
        compute the lattice of flats of a matroid or ordered matroid
    Usage
        L = latticeOfFlats(M)
        L = latticeOfFlats(OM)
    Inputs
        M:Matroid 
        OM:OrderedMatroid
        Reduced => Boolean
            whether to remove the top element and bottom element from the 
            lattice
    Outputs
        L:Poset
            the (reduced) lattice of flats
    Description
        Text
            The lattice of flats of a matroid M is the @TO poset@ of @TO 
            flats@ of a matroid M ordered by inclusion. This poset is an 
            atomistic, semimodular lattice having the empty set as the unique 
            minimal element and the @TO2 {ground,"ground set"}@ as unique 
            maximal element. By default the method @TO latticeOfFlats@ returns 
            the lattice of flats without the minimal and maximal elements; 
            this behavior can be modified with the option @TO Reduced@.
        Example
            M = matroid completeGraph 3;
            P = latticeOfFlats M;
            L = latticeOfFlats (M, Reduced => false);
            minimalElements P --the atoms of L
            isLattice L
            isAtomic dual L
            isLowerSemimodular L
            isUpperSemimodular L
        Text
            When applied to an @TO2 {orderedMatroid, "ordered matroid"}@ this 
            method returns the lattice of flats of the underlying unordered 
            matroid but with each flat ordered with respect to the linear 
            ordering on the ground set. This is useful, for example, when 
            inducing monomial orders on the @TO2 {matroidChowRing,"Chow 
            ring"}@ associated to an (unordered) matroid.
        Example
            Q = latticeOfFlats orderedMatroid (M,{2,1,0})
            isomorphism(P,Q)
    SeeAlso
        closure
        flats
        isAtomic
        isLowerSemimodular
        isUpperSemimodular
        matroidChowIdeal
        matroidChowRing
///

doc ///
    Key
        LatticeOfFlats
    Headline
        key for the lattice of flats of a matroid
    Usage
        M.cache.LatticeOfFlats
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        L:Poset
            the reduced lattice of flats of a matroid, if computed
    Description
        Text
            If the method @TO latticeOfFlats@ has been applied to a @TO 
            matroid@ then then resulting poset is stored in the matroid cache
            and can be retrieved as follows.
        Example
            MK3 = matroid completeGraph 3;
            latticeOfFlats MK3;
            MK3.cache.LatticeOfFlats
    SeeAlso
        latticeOfFlats
///

doc ///
    Key
        parallelClasses
        (parallelClasses, Matroid)
        (parallelClasses, OrderedMatroid)
    Headline
        compute the parallel classes of a matroid
    Usage
        P = parallelClasses M
        P = parallelClasses OM
    Inputs
        OM:OrderedMatroid
        M:Matroid
    Outputs
        :List
    Description
        Text
            Computes the parallel classes of a(n ordered) matroid, 
            that is, the (ordered) @TO flats@ of @TO2 {rk, "rank"}@ one.
        Example
            MK4 = matroid completeGraph 4
            M = contraction_(MK4) {5}
            parallelClasses M
    SeeAlso
        (symbol ==, OrderedMatroid, OrderedMatroid)
        contraction
        flats
        orderedFlats
///

doc ///
    Key
        matroidIndependenceComplex
        ComputePoset
        (matroidIndependenceComplex, Matroid, Ring)
        (matroidIndependenceComplex, Matroid)
        (matroidIndependenceComplex, OrderedMatroid, Ring)
        (matroidIndependenceComplex, OrderedMatroid)
        [matroidIndependenceComplex, ComputePoset]
    Headline
        the independence complex of a matroid or ordered matroid
    Usage
        Delta = matroidIndependenceComplex (M,R)
        Delta = matroidIndependenceComplex (M)
        Delta = matroidIndependenceComplex (OM,R)
        Delta = matroidIndependenceComplex (OM)
    Inputs
        M:Matroid
        OM:OrderedMatroid
        R:Ring
            any field is permissible
        ComputePoset=>Boolean
            whether to cache the simplicial complex as a poset  
    Outputs
        Delta:SimplicialComplex
    Description
        Text
            The @TO2 {independents,"independent sets"}@ of a matroid M form a 
            simplicial complex, called the independence complex M, whose 
            maximal elements (a.k.a. @TO facets@) are the bases of the matroid.
            Once computed, the complex is stored in the matroid cache.
        Example
            MK3 = matroid completeGraph 3;
            Delta = matroidIndependenceComplex MK3;
            peek Delta
            peek MK3.cache
        Text
            To work over a field other than the rationals simply include it in 
            the input data.
        Example
            Delta' = matroidIndependenceComplex (MK3, ZZ/2);
            peek Delta'
        Text
            Applying this method to an @TO2 {orderedMatroid,"ordered 
            matroid"}@ returns an isomorphic simplicial complex. The main 
            difference is that the variables in the underlying ring preserve 
            the ordering on the ground set of the ordered matroid. Unlike for 
            matroids, the independence complex of an ordered matroid is stored
            in M.@TO Presentations@.
        Example
            OMK3 = orderedMatroid (MK3, {2,1,0})
            matroidIndependenceComplex OMK3;
            peek OMK3.Presentations
        Text
            Occasionally it is useful to view the independence complex of a 
            matroid as a @TO2 {Poset, "poset"}@. To obtain this poset use the 
            option @TO ComputePoset@.
        Example
            matroidIndependenceComplex (MK3, ComputePoset => true);
            peek MK3.cache
            matroidIndependenceComplex (OMK3, ComputePoset => true);
            peek OMK3.Presentations
        Text
            Typically when one speaks of the f- and h-vectors of a matroid, 
            one is referring to the f- and h-vectors of the independence 
            complex. The @TO2 {fVector, "f-vector"}@ can be computed directly 
            while the h-vector can be obtained (in polynomial form) as the 
            numerator of the @TO2 {reduceHilbert, "reduced"}@ @TO2 
            {hilbertSeries, "Hilbert series"}@ of the face (a.k.a. 
            Stanley-Reisner) ring of Delta.
        Example
            fVector Delta
            numerator reduceHilbert hilbertSeries Delta.faceIdeal
        Text 
            The last computation is so common that we provide the method @TO 
            matroidHPolynomial@ for computing it directly.
        Example
            matroidHPolynomial MK3
            matroidHPolynomial orderedMatroid (MK3, {2,1,0})        
    Caveat
        The @TO Matroids@ package defines the @TO2 {fvector,"f-vector"}@ of a 
        matroid to be the (coefficients of) the rank generating function of 
        the (non-reduced) @TO2 {latticeOfFlats,"lattice of flats"}@. Thus @TO 
        fvector@ and @TO matroidFVector@ encode different data.
    SeeAlso
        faceIdeal
        fvector
        fVector
        matroidFVector
        matroidHPolynomial
///

doc ///
    Key
        IndependenceComplex
    Headline
        the independence complex of a matroid
    Usage
        M.cache.IndependenceComplex
        OM.Presentations
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        :SimplicialComplex
    Description
        Text
            Once the method @TO matroidIndependenceComplex@ has been applied 
            to a matroid M, the resulting simplicial complex can be found in 
            the matroid cache under the key @TO IndependenceComplex@.
        Example
            M := matroid completeGraph 3;
            peek M.cache
            matroidIndependenceComplex M;
            peek M.cache
        Text
            When working with @TO2 {orderedMatroid, "ordered matroids"}@, the 
            independence complex can be found in @TO Presentations@.
        Example
            M := orderedMatroid completeGraph 3;
            peek M.cache
            matroidIndependenceComplex M;
            peek M.cache
    SeeAlso
        matroidIndependenceComplex
///

doc ///
    Key
        complexAsPoset
    Headline
        a matroid independence complex stored as a poset
    Usage
        M.cache.complexAsPoset
        OM.Presentations.complexAsPoset
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        :Poset
    Description
        Text
            A simplicial complex on n elements can be viewed as a subposet of 
            the Boolean lattice. Setting the option @TO ComputePoset@ to true 
            when computing the @TO2 {matroidIndependenceComplex, "independence 
            complex"}@ of a matroid M, one can store this poset in the matroid 
            cache under the key @TO complexAsPoset@.
        Example
            M = matroid completeGraph 3;
            matroidIndependenceComplex (M, ComputePoset => true);
            peek M.cache
        Text
            Similary, for an ordered matroid the poset is stored in the @TO 
            Presentations@ cache.
        Example
            M = orderedMatroid completeGraph 3;
            matroidIndependenceComplex (M, ComputePoset => true);
            peek M.Presentations    
    SeeAlso
        Presentations
        matroidIndependenceComplex
        isMatroidIndependenceComplex
///

doc ///
    Key
        matroidTuttePolynomial
        (matroidTuttePolynomial, OrderedMatroid)
        (matroidTuttePolynomial, Matroid)
    Headline
        compute the Tutte polynomial of a matroid
    Usage
        T = matroidTuttePolynomial (OM)     
        T = matroidTuttePolynomial (M)
    Inputs
        OM:OrderedMatroid
        M:Matroid
    Outputs
        T:RingElement
            the Tutte polynomial of a matroid
    Description
        Text
            The Tutte polynomial of an @TO2 {orderedMatroid, "ordered 
            matroid"}@ OM is the bivariate polynomial given by $\sum x^{i(
            B)}y^{e(B)}$, where the sum is over all @TO2 {orderedBases, 
            "ordered bases"}@ of OM and where $i(B)$ and $e(B)$ are the number 
            of @TO2 {internallyActiveElements, "internally active"}@, 
            respectively @TO2 {externallyActiveElements, "externally 
            active"}@, elements of the basis $B$. While this definition 
            requires the choice of an ordering of the ground set, the Tutte 
            polynomial itself is independent from from this choice.
        Example
            MK3 = orderedMatroid completeGraph 3;
            tally apply (
                permutations 3, 
                p -> matroidTuttePolynomial orderedMatroid (MK3.matroid, p)
                )
        Text
            Note that Macaulay2 does not recognize these polynomials as being 
            the same because they are elements of different @TO2 {instance, 
            "instances"}@ of the ring ZZ[x,y]. Naming an instance of the ring 
            and @TO2 {sub, "substituting"}@ each polynomial into the named 
            ring gives the desired result.
        Example
            R := ZZ[x,y];
            tally apply (
                permutations 3, 
                p -> sub(
                    matroidTuttePolynomial orderedMatroid (MK3.matroid, p),
                    R)
                )
        Text
            When applied to an unordered matroid M, this method treats M as an 
            ordered matroid with the natural ordering on the ground set.
        Example
            matroidTuttePolynomial (MK3.matroid)    
        Text
            @TO matroidTuttePolynomial@ is not the first method for obtaining 
            the Tutte polynomial of an object in Macaulay2. We briefly discuss 
            the other methods available and how they compare with the method 
            in this package.

            The @TO Matroids@ package has two methods for determining the 
            Tutte polynomial of a matroid: @TO tuttePolynomial@ and @TO 
            tutte2@. As the next example shows, these methods can give 
            different results, with our @TO matroidTuttePolynomial@ agreeing 
            with the latter.
        Example
            M = matroid transpose matrix {{1,0},{0,1},{1,1},{1,1}};
            tuttePolynomial M
            tutte2 M
            matroidTuttePolynomial M
        Text
            Rather surprisingly neither the @TO HyperplaneArrangements@ nor 
            the @TO Graphs@ package allows one to compute the Tutte polynomial 
            of the classes defined therein. This package remedies these 
            omissions.
        Example
            matroidTuttePolynomial orderedMatroid completeGraph 3
            matroidTuttePolynomial orderedMatroid typeA(2)
        Text
            Finally we mention that the @TO Poset@ package has a method for 
            computing the Tutte polynomial of a poset. The documentation for 
            that method (see the link in SeeAlso below) does not give the 
            working definition but the following example shows that it cannot 
            be the definition given in [Go93].
        Example
            M = matroid completeGraph 3;
            -- get all independent sets of I as a list
            G = unique flatten apply(M.bases, b-> subsets b);
            -- order them by inclusion
            P = poset (G, (I1,I2) -> isSubset(I1,I2)) 
            degree Posets$tuttePolynomial P == degree tuttePolynomial M
        Text
            {\bf References}@BR{}@

            @UL{
                "[Go93] A Tutte polynomial for Partially Ordered Sets  (G. 
                Gordon,1993)"
            }@      
    SeeAlso
        tuttePolynomial
        tutte2
        Posets$tuttePolynomial          
///

doc ///
    Key
        matroidHPolynomial
        (matroidHPolynomial, Matroid)
        (matroidHPolynomial, OrderedMatroid)
    Headline
        compute the h-polynomial of a matroid or ordered matroid
    Usage
        matroidHPolynomial (M)
        matroidHPolynomial (OM)
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        :RingElement
            the h-polynomial of the @TO2 {matroidIndependenceComplex, 
            "independence complex"}@ of a matroid 
    Description
        Text
            The h-vector of a @TO2 {simplicialComplex, "simplicial complex"}@ 
            $\Delta$ is a certain linear transformation of its @TO2 {fVector, 
            "f-vector"}@. It is an elementary result in the theory of @TO2 
            {faceIdeal, "face rings"}@ (a.k.a., Stanley-Reisner rings) that 
            the entries of the h-vector are encoded as the coefficients of the 
            numerator of the @TO2 {hilbertSeries,"Hilbert series"}@ of the 
            @TO2 {faceIdeal,"face ring"}@ of $\Delta$.

            For a matroid M (@TO2 {orderedMatroid, "ordered"}@ or @TO2 
            {matroid, "not"}@), the method @TO matroidHPolynomial@ computes 
            the numerator of the @TO2 {reduceHilbert, "reduced"}@ Hilbert 
            series of the face ring of the @TO2 {matroidIndependenceComplex, 
            "independence complex"}@ of M.
        Example
            MK4 = orderedMatroid completeGraph 4;
            h = matroidHPolynomial MK4
        Text
            The degree of the h-polynomial of a matroid M is equal to 
            the @TO2 {rk,"rank"}@ of the matroid minus the number of @TO2 
            {coloops, "coloops"}@ of M. For example, if r > 0 then every 
            element of the @TO2 {uniformMatroid,"uniform matroid"}@ U(r,r) is 
            a coloop and the h-polynomial is the constant polynomial 1.
        Example
            matroidHPolynomial uniformMatroid (1,1)
            matroidHPolynomial uniformMatroid (2,2)
            matroidHPolynomial uniformMatroid (3,3)
        Text    
            By a result of Las Vergnas in [LV01], the @TO2 
            {rankGeneratingFunction, "rank generating function"}@ of the @TO2 
            {internalOrder, "internal order"}@ of an @TO2 {orderedMatroid, 
            "ordered matroid"}@ M and the matroid h-polynomial of M coincide.
        Example
            MK4 = orderedMatroid completeGraph 4
            time rankGeneratingFunction internalOrder MK4
            time matroidHPolynomial MK4
        Text
            {\bf References}@BR{}@

            @UL{
                "[LV01] Active Orders for Matroid Bases  (M. Las Vergnas,
                2001)"
            }@  
    SeeAlso 
        matroidIndependenceComplex
        matroidFVector
        internalOrder
///

doc ///
    Key
        matroidFVector
        (matroidFVector, Matroid)
        (matroidFVector, OrderedMatroid)
    Headline
        compute the f-vector of the independence complex of a matroid
    Usage
        f = matroidFVector (M)
        f = matroidFVector (OM)
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        f:HashTable
    Description
        Text
            The i-th entry of the f-vector of a @TO2 {simplicialComplex, 
            "simplicial complex"}@ $\Delta$ encodes the number of faces of 
            $\Delta$ of dimension i. Given a matroid M, the method @TO2 
            {matroidFVector,"matroidFVector"}@ computes the f-vector of the 
            @TO2 {matroidIndependenceComplex,"independence complex"}@ of M.
        Example
            matroidFVector matroid completeGraph 3
    SeeAlso
        matroidHPolynomial
        matroidIndependenceComplex
///

doc ///
    Key
        matroidChowIdeal
        (matroidChowIdeal, Matroid, Ring)
        (matroidChowIdeal, Matroid)
        
    Headline
        compute the defining ideal of the Chow ring of a matroid
    Usage
        I = matroidChowIdeal (M,R)
        I = matroidChowIdeal (M)
    Inputs
        M:Matroid
        R:Ring
            a field of characteristic zero
    Outputs
        I:Ideal
            the defining relations of the Chow ring of a matroid
    Description
        Text
            Given a matroid M, let R be the polynomial ring over the reals 
            with one indeterminate for each nonempty proper @TO2 {flats, 
            "flat"}@ of M. The Chow ideal C of M is the sum I + J where 
            @BR{}@ @BR{}@
            (1) I is the ideal generated by the binomials x_fx_g where f and g 
            are incomparable flats in the @TO2 {latticeOfFlats,"lattice of 
            flats"}@ of M, and @BR{}@ @BR{}@
            (2) J is the ideal generated by the linear forms S_a - S_b where 
            S_a is the sum of all indeterminates x_f such that f is a flat of 
            M containing the element a of the @TO2 {ground, "ground set"}@ (
            and similarly for S_b).

            The method @TO2 {matroidChowIdeal,"matroidChowIdeal"}@ produces 
            this ideal.
        Example
            MK3 = matroid completeGraph 3;
            I = matroidChowIdeal MK3
            mingens I
        Text
            Notice that if no ring is provided the @TO2 {coefficientRing, 
            "coefficient ring"}@ is QQ. One can work over other rings as 
            follows.
        Example
            matroidChowIdeal (MK3, ZZ/2)        
        Text
            In [AHK15], this ideal and the corresponding @TO2 
            {matroidChowRing, "Chow ring"}@ are shown to satisfy the Hard 
            Lefschetz Theorem and the Hodge-Riemann relations from which it 
            follows that both the @TO2 {matroidFVector,"f-vector"}@ and the 
            absolute values of the coefficients appearing in the @TO2 
            {matroidCharacteristicPolynomial, "characteristic polynomial"}@ 
            are log-concave, settling two long-standing conjectures.

            {\bf References}@BR{}@

            @UL{
                "[AKH15] Hodge Theory for Combinatorial Geometries  (K. Adiprasito, J. Huh, and E. Katz, 2015)"
            }@
    SeeAlso
        latticeOfFlats
        matroidCharacteristicPolynomial
        matroidChowRing
        matroidFVector
///

doc ///
    Key
        matroidChowRing
        (matroidChowRing, Matroid, Ring)
        (matroidChowRing, Matroid)
      
    Headline
        compute the Chow ring of a matroid
    Usage
        S = matroidChowRing (M,R)
        S = matroidChowRing (M)
    Inputs
        M:Matroid
        R:Ring
    Outputs
        S:QuotientRing
            the Chow ring of M
    Description
        Text
            The Chow ring of a matroid M is obtained as the quotient S = R[F]/
            I where I is the @TO2 {matroidChowIdeal, "matroid Chow ideal"}@ 
            and R[F] is the polynomial ring with one variable for each 
            nonempty proper flat of M.
        Example
            matroidChowRing matroid completeGraph 3 
    SeeAlso
        flats
        latticeOfFlats
        matroidChowIdeal
///

doc ///
    Key
      matroidOrlikSolomon
      (matroidOrlikSolomon, OrderedMatroid)
    Headline
      compute the Orlik-Solomon algebra of an ordered matroid
    Usage
      A = matroidOrlikSolomon (OM)
    Inputs
      OM:OrderedMatroid
    Outputs
      A:QuotientRing
    Description
        Text
          Compute the Orlik-Solomon algebra of an ordered matroid OM. This 
          is a quotient of the exterior algebra generated by the @TO2 
          {orderedGround, "ordered ground set"}@ by the ideal generated by 
          boundaries of circuits of OM. See [OS80] and [LV01, Chapter 3].

          As the Orlik-Solomon algebra is a quotient of an exterior 
          algebra, it is a skew-commutative algebra.
        Example
          MK3 = orderedMatroid completeGraph 3;
          A = matroidOrlikSolomon MK3;
          isCommutative A
          isSkewCommutative A
        Text
          The numerator of the @TO2 {hilbertSeries, "Hilbert series"}@ of 
          the Orlik-Solomon algebra of an ordered matroid M encodes the same 
          information as the @TO2 {characteristicPolynomial, "characteristic 
          polynomial"}@ of the (full) @TO2 {latticeOfFlats, "lattice of 
          flats"}@ of M (see [OS80]).
        Example   
          time numerator reduceHilbert hilbertSeries A
          time characteristicPolynomial latticeOfFlats (MK3, Reduced => false)
        Text
          Working with rings in Macaulay2 is faster than working with 
          posets, so we compute the @TO2 {matroidCharacteristicPolynomial, 
          "characteristic polynomial"}@ of a matroid using the Orlik-Solomon 
          algebra.
        Example
          time matroidCharacteristicPolynomial MK3
        Text
          The monomials in the @TO2 {brokenCircuitComplex, "broken circuit 
          complex"}@ of a matroid correspond to a vector space basis for the 
          @TO2 {matroidOrlikSolomon, "Orlik-Solomon algebra"}@.
        Example
            nbc = brokenCircuitComplex MK3 
            B = basis matroidOrlikSolomon MK3
        Text
          {\bf References}@BR{}@

          @UL{
              "[LV01] Active Orders for Matroid Bases,  (M. Las 
              Vergnas, 2001)",
              "[OS80] Combinatorics and Topology of Complements of 
              Hyperplanes (P. Orlik and L. Solomon, 1980)"
              }@
    SeeAlso
      brokenCircuitComplex            
      matroidCharacteristicPolynomial
      orderedCircuits
///

doc ///
    Key
        brokenCircuitComplex
        (brokenCircuitComplex, OrderedMatroid, Ring)
        (brokenCircuitComplex, OrderedMatroid)
    Headline
        compute the broken circuit complex of a matroid
    Usage
        brokenCircuitComplex (M, R)
        brokenCircuitComplex (M)
    Inputs
        M:OrderedMatroid
        R:Ring
    Outputs
        :SimplicialComplex
    Description
        Text
            A broken circuit of an ordered matroid M is an ordered circuit 
            with the lexicographically smallest element removed. The broken 
            circuit complex of M is the @TO2 {simplicialComplex, "simplicial 
            complex"}@ on the @TO2 {orderedGround, "ordered ground set"}@ of 
            OM consisting of those subsets that do not contain a broken 
            circuit.
        Example
            MK3 = orderedMatroid completeGraph 3;
            nbc = brokenCircuitComplex MK3
        Text
            The broken circuit complex of an ordered matroid M is a subcomplex 
            of the @TO2 {matroidIndependenceComplex,"independence complex"}@ 
            of M. We check this for our example by showing that every 
            generator of the face ideal of the independence complex is in the 
            face ideal of the broken circuit complex.
        Example
            R = ring nbc;
            mic = matroidIndependenceComplex MK3;
            gens sub(mic.faceIdeal, R) % nbc.faceIdeal
        Text
            The faces of the broken circuit complex of an ordered matroid M 
            correspond to a basis for the @TO2 {matroidOrlikSolomon, 
            "Orlik-Solomon algebra"}@.
        Example
            B = basis matroidOrlikSolomon MK3
    SeeAlso
        matroidIndependenceComplex
        orderedCircuits
        matroidOrlikSolomon
///

doc ///
    Key
        matroidCharacteristicPolynomial
        (matroidCharacteristicPolynomial, Matroid)
        (matroidCharacteristicPolynomial, OrderedMatroid)
    Headline
        compute the characteristic polynomial of a matroid
    Usage
        matroidCharacteristicPolynomial M
        matroidCharacteristicPolynomial OM
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        :RingElement
    Description
        Text
            The characteristic polynomial of a matroid M is $X_M(q) = \sum 
            (-1)^S q^{r - r(S)}$ where the sum is over all subsets of the @TO2 
            {ground,"ground set"}@, $r$ is the @TO2 {rk,"rank"}@ of M, and $r(
            S)$ is the rank  of $S$ in M.
        Example
            MK4 = matroid completeGraph 4;
            matroidCharacteristicPolynomial MK4
        Text
            By [OS80, Theorem 2.6], the characteristic polynomial of a matroid 
            is essentially the numerator of the @TO2 {hilbertSeries, "Hilbert 
            series"}@ of the @TO2 {matroidOrlikSolomon, "Orlik-Solomon 
            Algebra"}@ of the corresponding ordered matroid.
        Example
            A = matroidOrlikSolomon orderedMatroid MK4;
            numerator reduceHilbert hilbertSeries A
        Text
            {\bf References}@BR{}@

            @UL{
                "[OS80] Combinatorics and Topology of Complements of 
                Hyperplanes (P. Orlik and L. Solomon, 1980)",
                }@  
    SeeAlso
        matroidOrlikSolomon
///

doc ///
    Key
        texInternalOrder
        (texInternalOrder, Poset)
        [texInternalOrder,Jitter]
    Headline
      generates a string containing a TikZ-figure of an internal order
    Usage
      texInternalOrder P
    Inputs
      P:Poset
          on elements of the form \{S,T,A\}
      Jitter=>Boolean 
    Outputs
      S:String
          a TikZ-figure of P
    Description
        Text
          This method adapts the @TO2 {Posets,"Posets"}@ method 
          @TO2 {texPoset,"texPoset"}@ to the task of rendering 
          visually appealing Hasse diagrams of internal orders in LaTeX 
          documents. In order for the rendering to succeed in LaTeX, include
          the TikZ package in the preamble of the LaTeX document.  

          For an @TO2 {OrderedMatroid,"ordered matroid"}@ M, let P be the 
          @TO2 {internalOrder,"internal order"}@ of M. The elements of the 
          @TO2 {GroundSet,"ground set"}@ of P are triples \{S,T,A\}, 
          see @TO2 {internalBasisDecomposition,"internalBasisDecomposition"}@.
          In the rendering provided by this method each such triple becomes 
          a string s^t_a consisting of the elements of their parent lists
          without commas or spaces separating them. 
          In particular, if an element of the triple is empty then so 
          is the corresponding element in the TeX string.
        Example
            P = internalOrder orderedMatroid completeGraph 3;
            texInternalOrder P
        Text
          For matroids on large ground sets (>10 elements), an element
          with more than one digits in its decimal expansion is underlined
          in the LaTeX string. This permits unambiguous rendering of 
          Hasse diagrams of internal orders of matroids with up to 99 
          elements. We illustrate with the internal order of the rank-1 matroid
          on 11 elements.
        Example
            Q = internalOrder orderedMatroid matrix {{1,1,1,1,1,1,1,1,1,1,1}};
            texInternalOrder Q
    SeeAlso
      texExternalOrder
      internalOrder
      externalOrder
///

doc ///
    Key
        texExternalOrder
        (texExternalOrder, Poset)
        [texExternalOrder, Jitter]
    Headline
      generates a string containing a TikZ-figure of an external order
    Usage
      texExternalOrder P
    Inputs
      P:Poset
          on elements of the form {B,Ext}
      Jitter=>Boolean 
    Outputs
      S:String
          a TikZ-figure of P
    Description
        Text
          This method adapts the @TO2 {Posets,"Posets"}@ method 
          @TO2 {texPoset,"texPoset"}@ method to the task of rendering 
          visually appealing Hasse diagrams of external orders in LaTeX 
          documents. In order for the rendering to succeed in LaTeX, include
          the TikZ package in the preamble of the LaTeX document.  

          For an @TO2 {OrderedMatroid,"ordered matroid"}@ M, let P be the @TO2 
          {externalOrder,"external order"}@ of M. The elements of the @TO2 
          {GroundSet,"ground set"}@ of P are pairs \{B,Ext\}, where B is a 
          basis of M and Ext consists of the externally active elements of B. 
          In the rendering provided by this method each such pair becomes a 
          string B_Ext consisting of the elements of their parent lists 
          without commas or spaces separating them. In particular, if an 
          element of the triple is empty then so is the corresponding element 
          in the TeX string. 
        Example
            P = externalOrder orderedMatroid completeGraph 3;
            texExternalOrder P
        Text
          For matroids on large ground sets (>10 elements), an element
          with more than one digits in its decimal expansion is underlined
          in the LaTeX string. This permits unambiguous rendering of 
          Hasse diagrams of external orders of matroids with up to 99 
          elements. We illustrate with the external order of the rank-1 matroid
          on 11 elements.

        Example
            Q = externalOrder orderedMatroid matrix {{1,1,1,1,1,1,1,1,1,1,1}};
            texExternalOrder Q
    SeeAlso
      texInternalOrder
      internalOrder
      externalOrder
///

doc ///
    Key
        isPavingMatroid
        (isPavingMatroid, Matroid)
        (isPavingMatroid, OrderedMatroid)
    Headline
        test if a matroid is paving
    Usage
        isPavingMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {rk, "rank"}@ r @TO2 {Matroid, "matroid"}@ M is paving if 
            every circuit of M has at least r elements. Equivalently, M is 
            paving if and only if M does not have the @TO2 {directsum, 
            "direct sum"}@ U(2,2) + U(0,1) as a minor.
        Example
            M = directsum (uniformMatroid (2,2), uniformMatroid (0,1));
            isPavingMatroid M
            isPavingMatroid dualMatroid M
        Text
            If a matroid is assigned to a user symbol then the value of this 
            method is stored in the matroid cache under the key 
            @TO IsPavingMatroid@.
        Example     
            peek M.cache
        Text
            The method can also be applied to @TO2 {orderedMatroid, 
            "ordered matroids"}@. 
        Example
            OM = orderedMatroid (completeGraph 3, {2,1,0});
            isPavingMatroid OM
            peek OM.matroid.cache
            OM.matroid.cache.IsPavingMatroid
    SeeAlso
        uniformMatroid
        hasMinor
///

doc ///
    Key
        IsPavingMatroid
    Headline
        Whether a matroid is paving or not
    Usage
        M.cache.IsPavingMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO2 
            {isPavingMatroid, "isPavingMatroid"}@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            peek M.cache
            isPavingMatroid M
            peek M.cache
    SeeAlso
        isPavingMatroid
///

doc ///
    Key
        isBinaryMatroid
        (isBinaryMatroid, Matroid)
        (isBinaryMatroid, OrderedMatroid)
    Headline
        test if a matroid is binary
    Usage
        isBinaryMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is binary if it is representable as 
            a vector configuration over @TO2 {GF, "GF(2)"}@. Equivalently, M 
            is binary if and only if M does not have @TO2 {uniformMatroid, 
            "U(2,4)"}@ as a @TO2 {hasMinor, "minor"}@.
        Example
            isBinaryMatroid uniformMatroid (2,4)
        Text
            If a matroid is assigned to a user symbol then the value of this 
            method is stored in the matroid cache under the key 
            @TO IsBinaryMatroid@.
        Example
            MK3 = matroid completeGraph 3;
            isBinaryMatroid MK3
            peek MK3.cache
        Text
            Notice that, as in the above example, when a matroid is binary 
            this method also adds the key @TO IsRepresentableMatroid@ to the 
            cache.

            The method can also be applied to @TO2 {orderedMatroid, 
            "ordered matroids"}@. 
        Example
            OM = orderedMatroid (completeGraph 3, {2,1,0});
            isBinaryMatroid OM
            peek OM.matroid.cache
            OM.matroid.cache.IsBinaryMatroid
    Caveat
        No attempt is made at producing a particular representation.        
    SeeAlso
        uniformMatroid
        hasMinor
        IsBinaryMatroid
///

doc ///
    Key
        IsBinaryMatroid
    Headline
        Whether a matroid is binary or not
    Usage
        M.cache.IsBinaryMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO2 
            {isBinaryMatroid, "isBinaryMatroid"}@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            peek M.cache
            isBinaryMatroid M
            peek M.cache
    SeeAlso
        isBinaryMatroid
///

doc ///
    Key
        isTernaryMatroid
        (isTernaryMatroid, Matroid)
        (isTernaryMatroid, OrderedMatroid)
    Headline
        test if a matroid is ternary
    Usage
        isTernaryMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is ternary if it is representable 
            as a vector configuration over @TO2 {GF, "GF(3)"}@. Equivalently, 
            M is ternary if and only if M does not have any of the following 
            as a @TO2 {hasMinor, "minor"}@: @TO2 {uniformMatroid, "U(2,5)"}@, 
            @TO2 {uniformMatroid, "U(3,5)"}@, the @TO2 {specificMatroids, 
            "fano matroid"}@, or its @TO2 {dualMatroid, "dual"}@.
        Example
            isTernaryMatroid uniformMatroid (3,5)
            isTernaryMatroid specificMatroids "fano"
        Text
            If a matroid is assigned to a user symbol then the value of this 
            method is stored in the matroid cache under the key 
            @TO IsTernaryMatroid@.
        Example
            MK3 = matroid completeGraph 3;
            isTernaryMatroid MK3
            peek MK3.cache
        Text
            Notice that, as in the above example, when a matroid is ternary 
            this method also adds the key @TO IsRepresentableMatroid@ to the 
            cache.
            
            The method can also be applied to @TO2 {orderedMatroid, 
            "ordered matroids"}@. 
        Example
            OM = orderedMatroid (completeGraph 3, {2,1,0});
            isTernaryMatroid OM
            peek OM.matroid.cache
            OM.matroid.cache.IsTernaryMatroid
    Caveat
        No attempt is made at producing a particular representation.
    SeeAlso
        hasMinor
        IsTernaryMatroid
        specificMatroids
        uniformMatroid
///

doc ///
    Key
        IsTernaryMatroid
    Headline
        whether a matroid is ternary or not
    Usage
        M.cache.IsTernaryMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO2 
            {isTernaryMatroid, "isTernaryMatroid"}@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            peek M.cache
            isTernaryMatroid M
            peek M.cache
    SeeAlso
        isTernaryMatroid
///

doc ///
    Key
        isGraphicMatroid
        (isGraphicMatroid, Matroid)
        (isGraphicMatroid, OrderedMatroid)
    Headline
        test if a matroid is graphic
    Usage
        isGraphicMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is graphic if it is representable 
            as the vector matroid of the @TO2 {signedIncidenceMatrix, "signed 
            incidence matrix"}@ of a (multi)@TO graph@. Equivalently, M is 
            graphic if and only if M does not have any of the following as a 
            @TO2 {hasMinor, "minor"}@: @TO2 {uniformMatroid, "U(2,4)"}@, the 
            dual matroid of the cycle matroid of @TO2 {completeGraph, "K_5"}@, 
            the dual matroid of the cycle matroid of @TO2 
            {completeMultipartiteGraph, "K_{(3,3)}"}@, the @TO2 
            {specificMatroids, "fano matroid"}@, or its @TO2 {dualMatroid, 
            "dual"}@.
        Example
            isGraphicMatroid uniformMatroid (2,4)
            isGraphicMatroid specificMatroids "fano"
        Text
            If a matroid is assigned to a user symbol then the value of this 
            method is stored in the matroid cache under the key 
            @TO IsGraphicMatroid@.
        Example
            MK3 = matroid completeGraph 3;
            isGraphicMatroid MK3
            peek MK3.cache
        Text
            Notice that, as in the above example, when a matroid is graphic 
            this method also adds the keys @TO IsRegularMatroid@ and @TO 
            IsRepresentableMatroid@ to the cache.
            
            The method can also be applied to @TO2 {orderedMatroid, 
            "ordered matroids"}@. 
        Example
            OM = orderedMatroid (completeGraph 3, {2,1,0});
            isGraphicMatroid OM
            peek OM.matroid.cache
            OM.matroid.cache.IsGraphicMatroid
    Caveat
        No attempt is made at producing a particular representation.
    SeeAlso
        hasMinor
        IsGraphicMatroid
        specificMatroids
        uniformMatroid
///

doc ///
    Key
        IsGraphicMatroid
    Headline
        whether a matroid is graphic or not
    Usage
        M.cache.IsGraphicMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO2 
            {isGraphicMatroid, "isGraphicMatroid"}@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            peek M.cache
            isGraphicMatroid M
            peek M.cache
    SeeAlso
        isGraphicMatroid
///

doc ///
    Key
        isCographicMatroid
        (isCographicMatroid, Matroid)
        (isCographicMatroid, OrderedMatroid)
    Headline
        test if a matroid is cographic
    Usage
        isCographicMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is cographic if it is representable 
            as the dual of the vector matroid of the @TO2 
            {signedIncidenceMatrix, "signed incidence matrix"}@ of a 
            (multi)@TO graph@. Equivalently, M is cographic if and only if M 
            does not have any of the following as a @TO2 {hasMinor, "minor"}@: 
            @TO2 {uniformMatroid, "U(2,4)"}@, the the cycle matroid of @TO2 
            {completeGraph, "K_5"}@, the cycle matroid of @TO2 
            {completeMultipartiteGraph, "K_{(3,3)}"}@, the @TO2 
            {specificMatroids, "fano matroid"}@, or its @TO2 {dualMatroid, 
            "dual"}@.
        Example
            isCographicMatroid uniformMatroid (2,4)
            isCographicMatroid specificMatroids "fano"
        Text
            If a matroid is assigned to a user symbol then the value of this 
            method is stored in the matroid cache under the key 
            @TO IsCographicMatroid@.
        Example
            MK3 = matroid completeGraph 3;
            isCographicMatroid MK3
            peek MK3.cache
        Text
            Notice that, as in the above example, when a matroid is cographic 
            this method also adds the keys @TO IsRegularMatroid@ and @TO 
            IsRepresentableMatroid@ to the cache.
            
            The method can also be applied to @TO2 {orderedMatroid, 
            "ordered matroids"}@. 
        Example
            OM = orderedMatroid (completeGraph 3, {2,1,0});
            isCographicMatroid OM
            peek OM.matroid.cache
            OM.matroid.cache.IsCographicMatroid
    Caveat
        No attempt is made at producing a particular representation.
    SeeAlso
        hasMinor
        IsCographicMatroid
        specificMatroids
        uniformMatroid
///

doc ///
    Key
        IsCographicMatroid
    Headline
        whether a matroid is cographic or not
    Usage
        M.cache.IsCographicMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO2 
            {isCographicMatroid, "isCographicMatroid"}@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            peek M.cache
            isCographicMatroid M
            peek M.cache
    SeeAlso
        isCographicMatroid
///

doc ///
    Key
        isRegularMatroid
        (isRegularMatroid, Matroid)
        (isRegularMatroid, OrderedMatroid)
    Headline
        test if a matroid is regular
    Usage
        isRegularMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is regular if it is representable 
            over any field. Equivalently, M is regular if and only if M does 
            not have any of the following as a @TO2 {hasMinor, "minor"}@: @TO2 
            {uniformMatroid, "U(2,4)"}@, the @TO2 {specificMatroids, "fano 
            matroid"}@, or its @TO2 {dualMatroid, "dual"}@.
        Example
            isRegularMatroid uniformMatroid (2,4)
            isRegularMatroid specificMatroids "fano"
        Text
            If a matroid is assigned to a user symbol then the value of this 
            method is stored in the matroid cache under the key 
            @TO IsRegularMatroid@.
        Example
            MK3 = matroid completeGraph 3;
            isRegularMatroid MK3
            peek MK3.cache
        Text
            Notice that, as in the above example, when a matroid is regular 
            this method also adds the key @TO IsRepresentableMatroid@ to the 
            cache.
            
            The method can also be applied to @TO2 {orderedMatroid, 
            "ordered matroids"}@. 
        Example
            OM = orderedMatroid (completeGraph 3, {2,1,0});
            isRegularMatroid OM
            peek OM.matroid.cache
            OM.matroid.cache.IsRegularMatroid
    Caveat
        No attempt is made at producing a particular representation.
    SeeAlso
        hasMinor
        IsRegularMatroid
        specificMatroids
        uniformMatroid
///

doc ///
    Key
        IsRegularMatroid
    Headline
        whether a matroid is regular or not
    Usage
        M.cache.IsRegularMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO2 
            {isRegularMatroid, "isRegularMatroid"}@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            peek M.cache
            isRegularMatroid M
            peek M.cache
    SeeAlso
        isRegularMatroid
///

doc ///
    Key
        isRepresentableMatroid
        (isRepresentableMatroid, Matroid)
        (isRepresentableMatroid, OrderedMatroid)
    Headline
        test if a matroid is representable
    Usage
        isRepresentableMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is representable if it is 
            representable over some field. This method is very limited in 
            scope. It only tests whether the @TO IsRepresentableMatroid@ is 
            already in M.cache or if M.groundSet consists of the columns of a 
            matrix representing M. In the latter case it does not even check 
            if the induced matrix is a matrix over a field.
        Example
            M = matroid matrix {{1,2,3},{3,2,1}};
            isRepresentableMatroid M
            matrix {M.groundSet}
        Text
            If a matroid does not satisfy one of the conditions above, one can 
            try other tests such as @TO isBinaryMatroid@, @TO 
            isTernaryMatroid@, etc.
        Example
            MK3 = matroid completeGraph 3;
            isRepresentableMatroid MK3
            isGraphicMatroid MK3
            isRepresentableMatroid MK3    
    Caveat
        No attempt is made at producing a particular representation.
    SeeAlso
        isBinaryMatroid
        isGraphicMatroid
        isRegularMatroid
        IsRepresentableMatroid
        isTernaryMatroid
///

doc ///
    Key
        IsRepresentableMatroid
    Headline
        whether a matroid is representable or not
    Usage
        M.cache.IsRepresentableMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M any of a number 
            of methods have been applied to M.
        Example
            M = matroid completeGraph 3;
            isRepresentableMatroid M
            peek M.cache
            isGraphicMatroid M
            isRepresentableMatroid M
    SeeAlso
        isRepresentableMatroid
        isGraphicMatroid
        isRegularMatroid
        isBinaryMatroid
        isTernaryMatroid
///

doc ///
    Key
        signedIncidenceMatrix
        (signedIncidenceMatrix, Graph)
        [signedIncidenceMatrix, FullRank]
    Headline
        the signed incidence matrix of a graph
    Usage
        signedIncidenceMatrix G
    Inputs
        G:Graph
        FullRank=>Boolean
            whether the matrix should have full rank
    Outputs
        N:Matrix
    Description
        Text
            For a @TO graph@ G = ([n], E) on n vertices that is both simple 
            and undirected, the matrix N with n rows and edge many 
            columns having entries N_{ij} = e_i - e_j where i and j are in V, 
            ij is an edge in E, and j<i in the natural ordering on [n]. The 
            matrix N has rank n-1 and this methods defaults to presenting N as 
            a full rank matrix. This behavior is controlled with the option 
            @TO FullRank@ 
        Example
            signedIncidenceMatrix completeGraph 4
            signedIncidenceMatrix (completeGraph 4, FullRank => false)
    SeeAlso
        orderedMatroid
        Presentations
///

doc ///
    Key
        symbol FullRank
    Headline
        an option for signedIncidenceMatrix
    Usage
        signedIncidenceMatrix (G, FullRank => false)    
    Description
        Text
            See @TO signedIncidenceMatrix@.
///

doc ///
    Key
        IsInternallyPerfect
    Headline
        whether a matroid is internally perfect
    Usage
        M.cache.IsInternallyPerfect
    Inputs
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            When the method @TO isInternallyPerfect@ is applied to an ordered matroid M, the value is stored in the ordered matroid cache under the key @TO IsInternallyPerfect@.
        Example
            MK3 = orderedMatroid (completeGraph 3, {2,1,0});
            isInternallyPerfect MK3
            peek MK3.cache
    SeeAlso
        isInternallyPerfect
///

doc ///
    Key
        isSimpleMatroid
        (isSimpleMatroid, Matroid)
        (isSimpleMatroid, OrderedMatroid)
    Headline
        test if a matroid is simple
    Usage
        isSimpleMatroid M
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {Matroid, "matroid"}@ M is simple if it has no @TO loops@ 
            and no @TO2 {parallelClasses, "parallel elements"}@.
        Example
            m = matrix {{1,2,3},{3,2,1}}
            M = matroid m;
            isSimpleMatroid M
            n = m_{0,0,1,1,2}
            isSimpleMatroid matroid n
        Text
            Once the method isSimpleMatroid has been applied to a matroid, its 
            value is stored in the matroid cache under the key @TO 
            IsSimpleMatroid@.
        Example
            peek M.cache
            M.cache.IsSimpleMatroid
    SeeAlso
        loops
        parallelClasses
///

doc ///
    Key
        IsSimpleMatroid
    Headline
        whether a matroid is simple or not
    Usage
        M.cache.IsSimpleMatroid
    Inputs
        M:Matroid
        M:OrderedMatroid
    Outputs
        :Boolean
    Description
        Text
            A @TO2 {keys, "key"}@ in the cache of a matroid M once @TO 
            isSimpleMatroid@ has been applied to M.
        Example
            M = matroid completeGraph 3;
            isSimpleMatroid M
            peek M.cache
            isSimpleMatroid M
    SeeAlso
        isSimpleMatroid
        isGraphicMatroid
        isRegularMatroid
        isBinaryMatroid
        isTernaryMatroid
///

doc ///
    Key
        isMatroidIndependenceComplex
        (isMatroidIndependenceComplex, SimplicialComplex)
    Headline
        test if a simplicial complex is a matroid independence complex
    Usage
        isMatroidIndependenceComplex C
    Inputs
        C:SimplicialComplex
    Outputs
        :Boolean
    Description
        Text
            This method tests if a the @TO facets@ of a @TO2 
            {simplicialComplex, "simplicial complex"}@ satisfy the @TO2 
            {isValid, "basis exchange axiom"}@ of a @TO matroid@. 
        Example
            R = ZZ[a..f];
            I = monomialIdeal (a*f, b*d, c*e);
            C = simplicialComplex I;
            isMatroidIndependenceComplex C
        Text
            If a simplicial complex is a matroid independence complex, then 
            one can use @TO orderedMatroid@ to convert the complex into an 
            ordered matroid. 
        Example
            OM = orderedMatroid C;
            peek OM.Presentations
        Text
            If the simplicial complex fails to be a matroid complex, then the 
            method will print a reason. For example, the following complex is 
            not @TO2 {isPure, "pure"}@ and hence cannot be the independence 
            complex of a matroid.
        Example
            J = monomialIdeal (a*b*c, a*e*f);
            D = simplicialComplex J;
            isMatroidIndependenceComplex D
        Text
            The following simplicial complex is not a matroid complex because 
            its facets do not satisfy the basis exchange axiom. 
        Example
            K = simplicialComplex {a*b, c*d, e*f};
            isMatroidIndependenceComplex K  
    SeeAlso
        SimplicialComplex
        isValid
        matroidIndependenceComplex
        orderedMatroid
///

doc ///
    Key
        betaInvariant
        (betaInvariant, Matroid)
        (betaInvariant, OrderedMatroid)
    Headline
        the beta invariant of a matroid
    Usage
        betaInvariant M
        betaInvariant OM
    Inputs
        M:Matroid
        OM:OrderedMatroid
    Outputs
        :ZZ
    Description
        Text
            The beta invariant of a matroid M is defined to be (-1)^r X'(1) 
            where r is the rank of M and X' is the derivative of the @TO2 
            {matroidCharacteristicPolynomial, "characteristic polynomial"}@ of 
            M. The beta invariant of a matroid M is always a nonnegative 
            integer. If M is not empty or a @TO2 {loops, "loop"}@, then its 
            beta invariant is zero if and only if M is @TO2 {componentsOf, 
            "disconnected"}@.
        Example
            MK3 = matroid completeGraph 3;
            betaInvariant MK3
            betaInvariant directsum (MK3,MK3)
        Text
            If M is not a coloop, then its beta invariant equals one if and 
            only if M is the cycle matroid of a series-parallel network.

            The beta invariant can be used in many cases to check if two 
            matroids are dual. This is because if M has no loops nor coloops, 
            then its beta invariant and that of its dual coincide.
        Example
            betaInvariant dualMatroid MK3 == betaInvariant MK3  
    SeeAlso
        matroidCharacteristicPolynomial
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
assert(M.orderedCocircuits === {{1, 2}, {1, 0}, {2, 0}})
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
-- matroidHPolynomial
M = orderedMatroid (matroid completeGraph 3,{1,2})
R = ZZ[q]
assert(toString (matroidHPolynomial M.matroid) === toString(q^2+q+1))
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

