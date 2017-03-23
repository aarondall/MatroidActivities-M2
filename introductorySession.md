# **MatroidActivities** #
A package for working with ordered matroids in Macaulay2.

<!-- MarkdownTOC -->

- [History][history]
- [The Package][the-package]
	- [Computing with Matroids in MatroidActivities][computing-with-matroids-in-matroidactivities]
		- [Algebraic Constructions with Unordered Matroids][algebraic-constructions-with-unordered-matroids]
		- [Combinatorial Constructions with Unordered Matroids][combinatorial-constructions-with-unordered-matroids]
		- [Tests for Unordered Matroids][tests-for-unordered-matroids]
	- [Computing with Ordered Matroids in MatroidActivities][computing-with-ordered-matroids-in-matroidactivities]
		- [Algebraic Constructions with Ordered Matroids][algebraic-constructions-with-ordered-matroids]
		- [Combinatorial Constructions with Ordered Matroids][combinatorial-constructions-with-ordered-matroids]
		- [Tests for Ordered Matroids][tests-for-ordered-matroids]
	- [Internally Perfect Matroids and Stanley's Conjecture][internally-perfect-matroids-and-stanleys-conjecture]
		- [Stanley's Conjecture][stanleys-conjecture]
		- [An Interesting Internally Perfect Matroid][an-interesting-internally-perfect-matroid]

<!-- /MarkdownTOC -->


<a name="history"></a>
## History ##

[Macaulay2][M2] is an excellent tool to get intuition and refine conjectures when studying algebraic geometry and commutative algebra. I first came to use it when I needed some higher dimensional examples of curious polyhedral subdivisions of a space-tiling zonotopes. Typically when I want to compute polyhedral subdivsions these days I turn to [polymake][polymake] but back then installing polymake on my Mac was beyond me, so out of desperation I turned to the [Polyhedra][Polyhedra] package of Macaulay2 written by [René Birkner][Birkner]. The package was intuitive to use and the documentation was excellent (a common feature of Macaulay2 packages). After a couple of weeks running examples, [Julian Pfeifle][Pfeifle] and I found the right formulation for the result that appears as the main theorem in our paper [A Polyhedral Proof of the Matrix Theorem](https://arxiv.org/abs/1404.3876).

That project with Julian got me thinking about matroids and I ended up writing some simple scripts in Macaulay2 to facilitate the research that eventually led to the article [Internally Perfect Matroids](https://arxiv.org/abs/1510.04532). In some sense, this package can be seen as the companion software to that article.

Much later I found the [Matroids][Matroids] package written by [Justin Chen's][Chen] and set about recasting my scripts to fit with the vast amount of work he had done. The result is the package [MatroidActivities][MA]. It both expands the functionality available for studying (unordered) matroids in Macaulay2 and defines the new class **OrderedMatroid** for studying matroids endowed with a linear order on the ground set.

Following this link to [MatroidActivities][MA] one can find the source code and installation protocol. The goals of this post are twofold: to highlight some of the features available with this package and to illustrate these features by working out in detail Example 6 in [Internally Perfect Matroids](https://arxiv.org/abs/1510.04532).

<a name="the-package"></a>
## The Package ##

As of March 2017, the current release is [MatroidActivities][MA] 0.2. The package is still under development. Please get in touch with any comments, feature requests, or bug reports!

[MatroidActivities][MA] facilitates studying matroids on the Macaulay2 platform in two major ways. First, it extends the functionality of the [Matroids][Matroids] package by defining a number of new methods for creating matroids, producing matroid invariants, and testing a given matroid for certain properties. Second, it defines a new class of objects, the **OrderedMatroid** class, that allows the user to study structures arising from matroids whose ground sets have been endowed with a linear order. Such structures include the [broken circuit complex][BCC], the [Orlik-Solomon algebra][OSA], and (of course) [internal][LV] and [external activities][LV].

We will first talk about the new methods available for unordered matroids before turning to those available for ordered matroids.

<a name="computing-with-matroids-in-matroidactivities"></a>
### Computing with Matroids in MatroidActivities ###

As stated above, [MatroidActivities][MA] builds upon the [Matroids][Matroids] package written by [J. Chen][Chen]. When loading MatroidActivites the Matroids package is automatically loaded (assuming the user has installed it) together with the following Macaulay2 packages: [HyperplaneArrangements][HA], [Posets][Posets], [SimplicialComplexes][SC], and [Depth][Depth].

One aspect of matroids that makes them so ubiquitous in mathematics is the many equivalent ways in which they can be defined: from graphs and matrices, as simplicial complexes, ideals, or posets with certain properties, etc. Using the Matroids package one can define a matroid from a list of bases or circuits, or from a graph or matrix. Using the `orderedMatroid` method, the MatroidActivities package allows the user to define matroids from these inputs as well as from (central) hyperplane arrangements, (monomial) ideals, and simplicial complexes. For example, below we obtain a(n ordered) matroid from the 2-dimensional braid arrangement.

	i1 : H = typeA 2; -- the 2-dimensional braid arrangement

	i2 : OM = orderedMatroid H; -- get the associated ordered matroid

	i3 : peek OM -- let's have a look under the hood

	o3 = OrderedMatroid{cache => CacheTable{...1...}                 }
                    matroid => Matroid
                    orderedBases => {{0, 1}, {0, 2}, {1, 2}}
                    orderedCircuits => {{0, 1, 2}}
                    orderedCocircuits => {{0, 1}, {0, 2}, {1, 2}}
                    orderedGround => {0, 1, 2}
                    Presentations => CacheTable{...2...}

We will talk about the difference between the class of matroids and ordered matroids below, but for now simply notice that the ordered matroid _OM_ is a hash table and one of the keys is `matroid`. Such a matroid object is always part of the data of an ordered matroid object and it can be retrieved as follows.

	i4 : M = OM.matroid; -- an object of type Matroid

	i5 : peek M -- matroids are also hash tables; use peek to view keys and values

	o5 = Matroid{bases => {set {0, 1}, set {0, 2}, set {1, 2}}}
	             cache => CacheTable{...2...}
	             ground => set {0, 1, 2}
	             groundSet => {| 1  |, | 1  |, | 0  |}
	                           | -1 |  | 0  |  | 1  |
	                           | 0  |  | -1 |  | -1 |

Generally speaking, a matroid is represented in Macaulay2 as a hash table with four keys:

+ **bases**: a list of (unordered) sets consisting of the bases of the matroid;
+ **ground**: a set of integers representing the indices of the ground set;
+ **groundSet**: the ground set of the matroid represented as a list of objects (integers, edges of a graph, or columns of a matrix);
+ **cache**: a place to store data computed about the matroid for quick recall later.

The above example will serve as a running example while we discuss the methods for the matroid class. We see that the matroid _M_ is a rank two matroid on 3 elements with three bases and that was defined by the columns of matrix. We can also see that the `cache` has two items in it already. We can view them and use them as in the next example.

	i6 : peek M.cache  -- viewing the cache

	o6 = CacheTable{circuits => {set {0, 1, 2}}}
                 nonbases => {}

	i7 : M.cache.circuits -- getting a value from the cache

	o7 = {set {0, 1, 2}}

	o7 : List

<a name="algebraic-constructions-with-unordered-matroids"></a>
#### Algebraic Constructions with Unordered Matroids ####

Now that we know the basics of how a matroid is structured in Macaulay2, let's try out some of the methods available in [MatroidActivities][MA]. As Macaulay2 is designed to study commutative algebra, it is natural to encode matroids as algebraic objects. One such object is the face ideal of the independence complex of a matroid, which is the ideal generated by the circuits of the matroid. We compute the independence complex of a matroid as follows.

<a name="i8"></a>

	i8 : C = matroidIndependenceComplex M

	o8 = | x_1x_2 x_0x_2 x_0x_1 |

	o8 : SimplicialComplex

Note that the monomials in `o8` are the facets of the independence complex, and that they correspond to the bases of _M_. When the independence complex of a matroid is computed its value is stored (together with its defining ideal) in the cache.

	i9 : peek M.cache

	o9 = CacheTable{CircuitIdeal => monomialIdeal(x x x )          }
                             	                   0 1 2
                circuits => {set {0, 1, 2}}
                IndependenceComplex => | x_1x_2 x_0x_2 x_0x_1 |
                nonbases => {}

Now any of Macaulay2 methods available for ideals and rings can be used to study our matroid. For example, it is well-known that the face ring of a matroid is **Cohen-Macaulay**. Let's confirm this for our example.

	i10 : I = M.cache.CircuitIdeal

	o10 = monomialIdeal(x x x )
	                     0 1 2

	o10 : MonomialIdeal of QQ[x , x , x ]
	                           0   1   2

	i11 : isCM (ring I /I)

	o11 = true

Two important invariants of a matroid are the _f_- and _h_-vectors of its independence complex. In this software, the _f_-vector is encoded as a hash table and the _h_-vector as a polynomial.

	i12 : matroidFVector M

	o12 = HashTable{-1 => 1}
	                0 => 3
	                1 => 3

	o12 : HashTable

	i13 : matroidHPolynomial M

	       2
	o13 = q  + q + 1

	o13 : ZZ[q]

Another useful algebraic construction is the [Chow ring of a matroid][AHK] which is a quotient of QQ[x<sub>F</sub>] with one variable for every nonempty proper flat.

	i14 : matroidChowIdeal M

	o14 = ideal (0, x   x   , x   x   , x   x   , 0, x    - x   , x    - x   , - x    + x   , x    - x   , - x    + x   , - x    + x   )
	                 {0} {1}   {0} {2}   {1} {2}      {0}    {1}   {0}    {2}     {0}    {1}   {1}    {2}     {0}    {2}     {1}    {2}

	o14 : Ideal of QQ[x   , x   , x   ]
	                   {0}   {1}   {2}

	i15 : matroidChowRing M

	                                                        QQ[x   , x   , x   ]
	                                                            {0}   {1}   {2}
	o15 = ------------------------------------------------------------------------------------------------------------------------
	      (0, x   x   , x   x   , x   x   , 0, x    - x   , x    - x   , - x    + x   , x    - x   , - x    + x   , - x    + x   )
	           {0} {1}   {0} {2}   {1} {2}      {0}    {1}   {0}    {2}     {0}    {1}   {1}    {2}     {0}    {2}     {1}    {2}

	o15 : QuotientRing

In a recent [paper][AHK], Adiprasito, Huh, and Katz used the Chow ring to prove two long-standing conjectures: for a simple matroid, both the _f_-vector of the independence complex and the _h_-polynomial of Orlik-Solomon algebra of a (simple) matroid are unimodal. We can confirm these facts by inspection for our toy example.

	i16 : print values matroidFVector M -- the f-vector `reversed'
	{3, 3, 1}

<a name="i17"></a>

	i17 : A = matroidOrlikSolomon orderedMatroid M; -- Orlik-Solomon algebra only accepts ordered matroids as input

	i18 : print numerator reduceHilbert hilbertSeries A
	           2
	1 + 3T + 2T

By a [classic result][OSA] the last polynomial is essentially the characteristic polynomial of the matroid.

	i19 : matroidCharacteristicPolynomial M

	                2
	o19 = 2 - 3T + T

	o19 : ZZ[T]

The beta invariant of a matroid is an evaluation of the derivative of the characteristic polynomial. It gives information about the connectedness of a matroid and is computed as follows.

	i20 : betaInvariant M

	o20 = 1

<a name="combinatorial-constructions-with-unordered-matroids"></a>
#### Combinatorial Constructions with Unordered Matroids ####

In the [MatroidActivities][MA] many of the algebraic constructions are considered as such since computing them using the algebraic methods in Macaulay2 leads to clean code and fast algorithms. Of course, from a theoretical standpoint many of them are purely combinatorial. For example, in this package the characteristic polynomial of a matroid is computed as a transformation of the Hilbert series of the Orlik-Solomon algebra. We could get the same result by computing the characteristic polynomial of the lattice of flats of a matroid, but this turns out to be much slower.

	i21 : time matroidCharacteristicPolynomial M
	     -- used 0.000092 seconds

	                2
	o21 = 2 - 3T + T

	o21 : ZZ[T]

	i22 : time characteristicPolynomial latticeOfFlats (M, Reduced => false)
	     -- used 0.002077 seconds

	       2
	o22 = q  - 3q + 2

	o22 : ZZ[q]

Nonetheless it is worth noting that both the lattice of flats and the Tutte polynomial of a matroid can be computed.

<a name="tests-for-unordered-matroids"></a>
#### Tests for Unordered Matroids ####

There are a number of methods included with [MatroidActivities][MA] for testing if a matroid belongs to a certain class. In Version 0.2 one can test if a matroid is simple, binary, ternary, regular, graphic, cographic, or paving. Once such a test has been run, its value is stored in the matroid cache. Let's check if our running example is a regular matroid. Before we run the test, let's look in on the cache.

	i23 : peek M.cache

	o23 = CacheTable{CircuitIdeal => monomialIdeal(x x x )          }
	                                                0 1 2
	                 circuits => {set {0, 1, 2}}
	                 IndependenceComplex => | x_1x_2 x_0x_2 x_0x_1 |
	                 LatticeOfFlats => Relation Matrix: | 1 0 0 |
	                                                    | 0 1 0 |
	                                                    | 0 0 1 |
	                 nonbases => {}

To check if M is regular we use the method `isRegularMatroid`.

	i24 : isRegularMatroid M

	o24 = true

	i25 : peek M.cache

	o25 = CacheTable{CircuitIdeal => monomialIdeal(x x x )          }
	                                                0 1 2
	                 circuits => {set {0, 1, 2}}
	                 IndependenceComplex => | x_1x_2 x_0x_2 x_0x_1 |
	                 IsBinaryMatroid => true
	                 IsRegularMatroid => true
	                 IsRepresentableMatroid => true
	                 IsTernaryMatroid => true
	                 LatticeOfFlats => Relation Matrix: | 1 0 0 |
	                                                    | 0 1 0 |
	                                                    | 0 0 1 |
	                 nonbases => {}

Note that the cache is now much more populated. This is because a matroid is regular if and only if it is binary and ternary, so the method adds the results of these subtests to the cache. Also, a matroid is regular if and only if it is representable over any field. The value of the key `IsRepresentableMatroid` captures this fact though there is no attempt to actually produce a representation.

Now we turn from computing with objects in the `Matroid` class to computing with those in the `OrderedMatroid` class.

<a name="computing-with-ordered-matroids-in-matroidactivities"></a>
### Computing with Ordered Matroids in MatroidActivities ###

We will now work with our small example viewed as an ordered matroid object instead of a matroid object. First we clear our previously defined symbols and redefine the hyperplane arrangement.

	i26 : clearAll -- deletes from memory all previously defined user symbols

	i27 : H = typeA 2; -- construct the 2-dim braid arrangement again

To construct an ordered matroid from a hyperplane arrangement (or a matroid, matrix, graph, etc.), call `orderedMatroid` on the pair `(X, L)` where X is an object of the appropriate type and L is a list giving the desired permutation of the ground set.

	i28 : OM = orderedMatroid (H, {2,0,1}); -- make the ordered matroid with 2 < 0 < 1

The result is an object of class OrderedMatroid. Objects in this class are hash tables, so we use `peek` to look at the data they contain.

	i29 : peek OM -- view the hash table representing the ordered matroid

	o29 = OrderedMatroid{cache => CacheTable{...1...}                 }
                     matroid => Matroid
                     orderedBases => {{2, 0}, {2, 1}, {0, 1}}
                     orderedCircuits => {{2, 0, 1}}
                     orderedCocircuits => {{2, 0}, {2, 1}, {0, 1}}
                     orderedGround => {2, 0, 1}
                     Presentations => CacheTable{...2...}

Five of the keys in this hash table are self-explanatory.

- **matroid**: the underlying matroid of the ordered matroid
- **orderedGround**: the linear ordering on the (indices of) the ground set of the matroid;
- **orderedBases**: the bases of the matroid ordered lexicographically using `orderedGround`;
- **orderedCircuits**: the circuits of the matroid ordered lexicographically using `orderedGround`;
- **orderedCocircuits**: the cocircuits of the matroid ordered lexicographically using `orderedGround`.

Now we look at the remaining keys. `Presentations` is a cache table which stores objects representing the given matroid in various classes. Our example came from a central hyperplane arrangement, so we should expect to see that arrangement in the table.

	i30 : peek OM.Presentations

	o30 = CacheTable{CentralArrangement => {x  - x , x  - x , x  - x }}
	                                         1    2   1    3   2    3
	                 Matrix => | 1  1  0  |
	                           | -1 0  1  |
	                           | 0  -1 -1 |

Indeed, `OM.Presentations.CentralArrangement` exists in the table. Moreover, we have a matrix representation of `OM` that was made behind the scenes when we created the ordered matroid from the hyperplane arrangement. The keys that can possibly appear in the Presentations cache are

	Matrix, Graph, CentralArrangement, SimplicialComplex, CircuitIdeal.

Finally, the **cache** key in an ordered matroid is a place to store data computed about the ordered matroid for quick access later. In our little example we have

	i31 : peek OM.cache

	o31 = CacheTable{isRepresentableMatroid => true}

*A word of warning*: Recall that a matroid is representable if it has a presentation as the columns of a matrix over a field. The key **isRepresentableMatroid** only indicates that, in the process of working with the matroid, some matrix presentation over a field has been computed.

Let's now turn to the algebraic constructions for ordered matroids provided by the [MatroidActivities][MA] package.

<a name="algebraic-constructions-with-ordered-matroids"></a>
#### Algebraic Constructions with Ordered Matroids ####

As for any matroid object, we can compute the independence complex of an ordered matroid.
<a name="i32"></a>

	i32 : C = matroidIndependenceComplex OM

	o32 = | x_0x_1 x_2x_1 x_2x_0 |

	o32 : SimplicialComplex

This simplicial complex is different than the one computed in [i8][i8], but only in a slightly subtle way. The monomial orders on the underlying rings are affected by the order in which the variables are presented. For the example from [i8][i8] the variables are ordered with respect to the natural order.

	i33 : gens ring matroidIndependenceComplex OM.matroid

	o33 = {x , x , x }
	        0   1   2

On the other hand, the order of the variables in the underlying ring of the complex C in [i32][i32] respects the linear order on the ground set of the ordered matroid OM.

	i34 : gens ring C

	o34 = {x , x , x }
	        2   0   1

A second ring one can construct from an ordered matroid is the [Orlik-Solomon algebra][OSA]. We have already used this construction above in [i17][i17]. Now let's take a look more closely. To create the Orlik-Solomon algebra of an ordered matroid use `matroidOrlikSolomon`.

	i35 : A = matroidOrlikSolomon OM;

This algebra is a quotient of the exterior algebra over the vector space generated by the flats of the matroid. As such, it is a skew-commutative (rather than commutative) algebra. We can see this as well as other structural properties by looking at the `options` of _A_.

	i36 : options A

	o36 = OptionTable{Constants => false                     }
	                  DegreeLift => null
	                  DegreeMap => null
	                  DegreeRank => 1
	                  Degrees => {{1}, {1}, {1}}
	                  Global => true
	                  Heft => {1}
	                  Inverses => false
	                  Join => null
	                  Local => false
	                  MonomialOrder => {MonomialSize => 32  }
	                                   {Weights => {0, 1, 2}}
	                                   {Weights => {1, 1, 1}}
	                                   {Lex => 3            }
	                                   {Position => Up      }
	                  SkewCommutative => {0, 1, 2}
	                  Variables => {e , e , e }
	                                 2   0   1
	                  WeylAlgebra => {}

	o36 : OptionTable

A second simplicial complex associated to any ordered matroid is the [(no) broken circuit complex][BCC]. It is a subcomplex of the independence complex and may be computed using the `brokenCircuitComplex` method.

	i37 : NBC = brokenCircuitComplex OM

	o37 = | x_2x_1 x_2x_0 |

	o37 : SimplicialComplex

For our small example, the broken circuit complex has two of the three (facets corresponding to) bases of _OM_ as facets. The third basis _x<sub>0</sub>x<sub>1</sub>_ is not a facet of the broken circuit complex because it is a broken circuit with respect to the ordering _2 < 0 < 1_.

The faces of the broken circuit complex of a matroid are a basis for the Orlik-Solomon algebra. To confirm this let's compute a basis of _A_.

	i38 : basis A

	o38 = | 1 e_2 e_2e_0 e_2e_1 e_0 e_1 |

	              1       6
	o38 : Matrix A  <--- A

Note that the monomials in the matrix above correspond to the faces of NBC.

<a name="combinatorial-constructions-with-ordered-matroids"></a>
#### Combinatorial Constructions with Ordered Matroids ####

In this section we turn to the methods included in [MatroidActivities][MA] that allow us to study internal and external activities in ordered matroids. We encourage the reader unfamiliar with these notions to consult Section 2 of Las Vergnas' [paper][LV].

By matroid duality internal and external activities are equivalent, so we will focus our attention here on internal activity. For the most part, every method available for computing internal activities has a counterpart for computing directly with external activities.

Given an ordered matroid _M_ on the ground set _E_ and a subset _A_ of  _E_, an element _e_ is **internally active** with respect to _A_ if _e_ is in _A_ and there is a cocircuit _C<sup>\*</sup>_ contained in _E - A \cup e_ such that _e_ is the least element of _C<sup>\*</sup>_. If _e_ is in  _A_ and is not internally active, then it is called **internally passive**.

Let's compute the internally active elements with respect to every subset of our running example. First let's view the ordered cocircuits.

	i41 : OM.orderedCocircuits

	o41 = {{2, 0}, {2, 1}, {0, 1}}

	o41 : List

Now we make a hash table whose keys are the subsets of the ordered ground set and whose values are the internally active elements.

	i42 : hashTable apply (subsets OM.orderedGround, s -> s => internallyActiveElements (OM,s))

	o42 = HashTable{{} => {}        }
	                {2} => {2}
	                {0} => {0}
	                {1} => {}
	                {2, 0} => {2, 0}
	                {2, 1} => {2}
	                {0, 1} => {}
	                {2, 0, 1} => {}

	o42 : HashTable

It is crucial to realize that internal activities depend on the ground set. For example, if we change the ordering of _OM_ to the natural ordering _0<1<2_ we obtain the following.

	i43 : OM' = (orderedMatroid (OM.matroid, {0,1,2}));

	i44 : OM'.orderedCocircuits

	o44 = {{0, 1}, {0, 2}, {1, 2}}

	o44 : List

	i45 : hashTable apply (subsets OM'.orderedGround, s -> s => internallyActiveElements (OM',s))

	o45 = HashTable{{} => {}        }
	                {0} => {0}
	                {1} => {1}
	                {2} => {}
	                {0, 1} => {0, 1}
	                {0, 2} => {0}
	                {1, 2} => {}
	                {0, 1, 2} => {}

	o45 : HashTable

When restricted to the bases of an ordered matroid the definition of internal activity can be restated as follows. An element _e_ in a basis _B_ is internally active if there is no lexicographically smaller basis (with respect to the linear order on the ground set) that contains _B - e_. The internal order of an ordered matroid _M_ is the poset _P_ on the basis of _M_ where two basis _B,B'_ of _M_ satisfy _B ≤ B'_ if every internally passive element of _B_ is internally passive in _B'_. The internal order of an ordered matroid can be computed using the method `internalOrder` which in turn uses methods from the [Posets][Posets] package written by Kristine Fisher, [Andrew Hoefel](https://scholar.google.com/citations?user=puuoR2MAAAAJ&hl=en), [Manoj Kummini](http://www.cmi.ac.in/~mkummini/), Stephen Sturgeon, and [Josephine Yu](http://people.math.gatech.edu/~jyu67/).

	i46 : internalOrder OM

	o46 = Relation Matrix: | 1 1 1 |
	                       | 0 1 1 |
	                       | 0 0 1 |

	o46 : Poset

We have noted that internal activity depends on the linear ordering of the ground set of the matroid. We should suspect that the internal order does as well. Let's count the number of isomorphism classes of internal orders of our running example as the linear order of the ground set varies over all permutations.

	i47 : # removeIsomorphicPosets apply (permutations 3, p -> internalOrder orderedMatroid (OM.matroid, p))

	o47 = 1

The fact that there one isomorphism class for our toy example is a fluke arising from the fact that the underlying matroid has exactly one cycle and so its internal order is a chain (for any ordering of its ground set). A more interesting example is provided by the cycle matroid of the complete graph on four vertices.

	i48 : M = matroid completeGraph 4;

	i49 : PP = removeIsomorphicPosets apply (permutations 6, p -> internalOrder orderedMatroid (M, p));

	i50 = #PP

	o50 = 3

This shows that, in general, the internal order of an ordered matroid is not an invariant of the underlying (unordered) matroid. On the other hand, there are properties of the internal order that are invariant under changes in the ordering on the ground set. The first is that the internal order is always a graded poset. Let's check this for all of the internal orders arising from _K_4_.

	i51 : all (PP, P -> isGraded P)

	o51 = true


The second important invariant property is that the internal order becomes a lattice once an artificial top element is added.

	i52 : all (PP, P -> isLattice adjoinMax (P))

	o52 = true

The third invariant property we will discuss is the rank generating function of the internal order. For any linear order of the ground set of a matroid, the rank generating function of the internal order is the _h_-polynomial of the matroid.

	i53 : matroidHPolynomial M

	        3     2
	o53 = 6q  + 6q  + 3q + 1

	i54 : apply (PP, P -> rankGeneratingFunction P)

	              3     2
	o54 = Tally{6q  + 6q  + 3q + 1 => 3}

We will investigate further this connection between the _h_-polynomial of a matroid and the rank generating function of the internal order in the final section below.

It is often useful to visualize a poset via its Hasse diagram. The `Posets` package has a method for visualizing an arbitrary poset in a LaTeX file. We have modified this method slightly to beautify the output for internal orders. The output of `texInternalOrder` can be cut and pasted directly into a LaTex file and the Hasse diagram will be rendered as long as `\usepackage{Tikz}` is included in the preamble.

	i55 : texInternalOrder internalOrder orderedMatroid M

	\tikzstyle{every node} = [draw = black, fill = white, rectangle, inner sep = 1pt]
	\begin{tikzpicture}[scale = 1]
	    \node (0) at (-0+0,0)    {\scriptsize_{{}^{}_{012}}_};
	    \node (1) at (-1.5+0,1.33333)    {\scriptsize_{{4}^{}_{01}}_};
	    \node (2) at (-1.5+1.5,1.33333)    {\scriptsize_{{5}^{}_{01}}_};
	    \node (3) at (-1.5+3,1.33333)    {\scriptsize_{{3}^{}_{02}}_};
	    \node (9) at (-3.75+0,2.66667)    {\scriptsize_{{4}^{2}_{1}}_};
	    \node (4) at (-3.75+1.5,2.66667)    {\scriptsize_{{5}^{2}_{0}}_};
	    \node (7) at (-3.75+3,2.66667)    {\scriptsize_{{45}^{}_{0}}_};
	    \node (8) at (-3.75+4.5,2.66667)    {\scriptsize_{{3}^{1}_{2}}_};
	    \node (5) at (-3.75+6,2.66667)    {\scriptsize_{{34}^{}_{0}}_};
	    \node (6) at (-3.75+7.5,2.66667)    {\scriptsize_{{35}^{}_{0}}_};
	    \node (12) at (-3.75+0,4)    {\scriptsize_{{45}^{1}_{}}_};
	    \node (15) at (-3.75+1.5,4)    {\scriptsize_{{45}^{2}_{}}_};
	    \node (13) at (-3.75+3,4)    {\scriptsize_{{34}^{2}_{}}_};
	    \node (10) at (-3.75+4.5,4)    {\scriptsize_{{34}^{1}_{}}_};
	    \node (14) at (-3.75+6,4)    {\scriptsize_{{35}^{2}_{}}_};
	    \node (11) at (-3.75+7.5,4)    {\scriptsize_{{35}^{1}_{}}_};
	  \foreach \to/\from in {0/1, 0/2, 0/3, 1/9, 1/5, 1/7, 2/4, 2/6, 2/7, 3/8, 3/5, 3/6, 4/14, 4/15, 5/13, 5/10, 6/14, 6/11, 7/12, 7/15, 8/10, 8/11, 9/13, 9/15}
	  \draw [-] (\to)--(\from);
	\end{tikzpicture}

In the rendered poset a bases _B_ is given as a triple _B = S^T_A_ where _A_ is the set of internally active elements of _B_ and the sets _S_ and _T_ are as follows. Let _B_0_ be the lexicographically least basis of the ordered matroid. Then _T_ (respectively, _S_) is the set of internally passive elements of _B_ that are (not) in _B_0_. In the above example the lexicographically least basis is _B_0 = \{0,1,2\}_. So the basis _\{0,2,5\}_ is has _A = \{0\}, T = \{2\}_ and _S= \{5\}_. We will use such decompositions of bases in what follows to define *internally perfect* bases and matroids.

*Note*: A LaTeX file containing Hasse diagrams of a representative for each of the three isomorphism classes of internal orders of _K_4_ can be found [here](https://raw.githubusercontent.com/aarondall/MatroidActivities-M2/master/img/internalOrders/internalOrdersK4.tex).

<a name="tests-for-ordered-matroids"></a>
#### Tests for Ordered Matroids ####

Let _M_ be an ordered matroid and _B = S^T_A_ be a basis, where _S,T,_ and _A_ are as in the previous section. Then _B_ is called an _f_-**principal basis** if there is an element _f \in E_ such that _S = \\{f\\}_.

There are some bases of every ordered matroid that can be written as the join (in the internal order) of _f_-principal bases in a unique way. Such bases are called (**internally**) **perfect bases**. For example, every _f_-principal basis is trivially perfect, as are those bases of the form _B = S^T_A_ where _T_ is the empty set. A basis that can be written as the join of _f_-principal bases in more than one way is called an **abundant** basis, while a basis that cannot be written as the join of _f_-principal bases is **deficient**. The method `basisType` allows one to test whether a basis is perfect, abundant, or deficient.

Let's check how many bases of each type the ordered matroid _K_4_ with the natural ordering has.

	i56 : OM = orderedMatroid M;

	i57 : tally apply (OM.orderedBases, B -> basisType (OM,B))

	o57 = Tally{abundant => 1 }
	            deficient => 1
	            perfect => 14

	o57 : Tally

So the complete graph on four vertices with the natural ordering on the edges furnishes an example in which all three basis types appear. A LaTeX file containing Hasse diagrams of a representative for each isomorphism class of internal orders of _K_4_ can be found [here](https://github.com/aarondall/MatroidActivities-M2/blob/master/internalOrdersK4.tex). In the next section we discuss ordered matroids which have only internally perfect bases. Such ordered matroids are called **internally perfect matroids** and were introduced in the article [Internally Perfect Matroids][Da]. One can test if an ordered matroid is internally perfect using the method `isInternallyPerfect`.

	i58 : isInternallyPerfect OM

	o58 = false

	i59 : isInternallyPerfect orderedMatroid completeGraph 3

	o59 = true


<a name="internally-perfect-matroids-and-stanleys-conjecture"></a>
### Internally Perfect Matroids and Stanley's Conjecture ###

In the previous section we saw how to compute basis types of an ordered matroid and that the bases of some matroids are all internally perfect. In this section we briefly discuss Stanley's Conjecture on the _h_-vectors of matroids and its connection with internally perfect matroids. Finally we use the methods in [MatroidActivities][MA] to exhibit an example of an internally perfect matroid that is not in any of the classes of matroids for which Stanley's Conjecture was previously known to hold.

<a name="stanleys-conjecture"></a>
#### Stanley's Conjecture  ####

In a 1977 [paper][ST], Richard Stanley showed that the _h_-polynomial of a matroid is an _\mathcal{O}_-sequence and conjectured that it is a *pure* _\mathcal{O}_-sequence. In other words the conjecture states that for any matroid _M_ there exists a collection of monomials _\mathbf{M}_ such that

 1. if _\mathbf{m} \in \mathbf{M}_ and _\mathbf{m}'_ divides _\mathbf{m}_, then _\mathbf{m}' \in \mathbf{M}_,
 2. the maximal elements of _\mathbf{M}_ (with respect to divisibility) all have the same total degree, and
 3. the number of elements of _\mathbf{M}_ with total degree _i_ equals the coefficient on _q^i_ in the _h_-polynomial of the matroid _M_.

Such a collection of monomials is called a *pure multicomplex*.

Stanley's Conjecture has spurred a great deal of research concerning _h_-polynomials of matroids and _\mathcal{O}_-sequences. It is known to hold for a rank _r_ matroid _M_ on _n_ elements with _c_ coloops if any of the following conditions hold:

 + _M_ is paving;
 + _h_s (M)~\le~5_, where _s = r - c_ is the degree of the _h_-polynomial;
 + _M^\*_ is graphic;
 + _M^\*_ is transversal;
 + _M^\*_ has no more than _n - r + 2_ parallel classes;
 + _n \le 9_ or _n-r \le 2_;
 + _r \le 4_; or
 + _M_ is internally perfect for some ordering of the ground set.

Let us call a matroid *interesting* if it is internally perfect but is not in any of the other classes listed above. The goal of the remainder of this section is to work out Example 6 from [Internally Perfect Matroids][DA] which shows that *interesting* matroids do exist.

<a name="an-interesting-internally-perfect-matroid"></a>
#### An Interesting Internally Perfect Matroid ####

Let _N_ be the ordered vector matroid given by the columns of the following matrix:

	i60 : mat = sub(matrix {{2, 1, 3, -1, -1, 0, -1, -1, 0, 3}, {1, 1, 1, 1, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 0, 0, -1, 1, 1, -1, 0}}, QQ)

	o60 = | 2 1 3 -1 -1 0  -1 -1 0  3 |
	      | 1 1 1 1  1  1  0  0  1  1 |
	      | 0 0 0 0  0  -1 1  1  -1 0 |

	               3        10
	o60 : Matrix QQ  <--- QQ

	i61 : N = orderedMatroid mat;

We are interested in the dual to the matroid _N_, but we point out that _N_ is an internally perfect matroid with respect to, for example, the order

	\\[{0, 3, 5, 1, 2, 4, 6, 7, 8, 9 }.\\]

We will show that the dual matroid _M = N^\*_ is *interesting*, that is, that it is internally perfect (and hence satisfies Stanley's Conjecture) and that it is not in any of the classes of matroids for which Stanley's Conjecture was previously known to hold. First we create _M_ and check that it is internally perfect with respect to the natural order on the ground set.

	i62 : M = orderedMatroid dualMatroid N.matroid;

	i63 : isInternallyPerfect M

	o63 = true

By the general theory for internally perfect matroids, it follows that the matroid _M_ satisfies Stanley's Conjecture since its internal order is isomorphic to a pure multicomplex (ordered by divisibility). We will now produce such a multicomplex. First consider the maximal elements in the Hasse diagram of the internal order of _M_.

![internal order][intOrd]

Since each of the maximal bases is internally perfect, there is a unique way to write each as a join of _f_-principal bases. We have

 + _B\_1 = 789^{1346}\_{\emptyset} = 7^{1346}\_{25} \vee 8^{\emptyset}\_{012346} \vee 9^{\emptyset}\_{013456}_

 + _B\_2 = 789^{1345}\_{\emptyset} = 7^{\emptyset}\_{012345} \vee 8^{1345}\_{26} \vee 9^{\emptyset}\_{013456}_

 + _B\_3 = 789^{2346}\_{\emptyset} = 7^{346}\_{025} \vee 8^{\emptyset}\_{012346} \vee 9^{2}\_{03456}_

 + _B\_4 = 789^{2345}\_{\emptyset} = 7^{\emptyset}\_{012345} \vee 8^{345}\_{026} \vee 9^{2}\_{03456}_

 + _B\_5 = 789^{1246}\_{\emptyset} = 7^{46}\_{0125} \vee 8^{\emptyset}\_{012346} \vee 9^{12}\_{3456}_

 + _B\_6 = 789^{1245}\_{\emptyset} = 7^{\emptyset}\_{012345} \vee 8^{45}\_{0126} \vee 9^{12}\_{3456}_

Notice that each internally passive element of a maximal basis occurs exactly once in the decomposition as joins of _f_-principal bases.

We now produce a pure multicomplex whose _\mathcal{O}_-sequence is precisely the _h_-vector of _M_. First we define a polynomial ring with variables indexed by those elements of the ground set of _M_ that are not in the lexicographically smallest basis.

	i64 : R = ZZ[x_7,x_8,x_9];

For a basis _B = S^T\_A_ and an _f \in S_ let _B\_f_ be the _f_-principal basis occurring in the decomposition of _B_ as a join of _f_-principal bases. For an _f_-principal basis of _M_ define the map _\mu_ into the polynomial ring _R_ via

\\[\mu(B_f) = x^{|IP(B_f)|}\_f.\\]

Since every basis of _M_ has a unique decomposition into a join of _f_-principal bases this map extends uniquely to a map on the bases of _M_. In our example we have

 + _B\_1 \mapsto x^5\_7 x\_8 x\_9_,

 + _B\_2 \mapsto x\_7 x\_8^5 x\_9_,

 + _B\_3 \mapsto x^4\_7 x\_8 x\_9^2_,

 + _B\_4 \mapsto x\_7 x\_8^4 x\_9^2_,

 + _B\_5 \mapsto x^3\_7 x\_8 x\_9^3_,

 + _B\_6 \mapsto x\_7 x\_8^3 x\_9^3_.

We store these monomials as a list.

	i65: maxMonomials = {x_7^5*x_8^1*x_9^1, x_7^1*x_8^5*x_9^1, x_7^4*x_8^1*x_9^2, x_7^1*x_8^4*x_9^2, x_7^3*x_8^1*x_9^3, x_7^1*x_8^3*x_9^3};

To create a multicomplex where these monomials are the maximal elements, we use the `divisorPoset` method from the `Posets` package. This creates a principal multicomplex from each of our maximal monomials. We then take the union of all of these to obtain our multicomplex.

	i66 : multicomplex = fold (union, apply (maxMonomials, m -> divisorPoset m))

This multicomplex is pure since its maximal elements all have the same total degree. Let's check that it has the correct _\mathcal{O}_-sequence using the `rankGeneratingFunction` method from the `Posets` package.

	i67 : rankGeneratingFunction multicomplex

	         7      6      5      4      3     2
	o67 = 6q  + 14q  + 15q  + 13q  + 10q  + 6q  + 3q + 1

	o67 : ZZ[q]

	i68 : matroidHPolynomial M

	         7      6      5      4      3     2
	o68 = 6q  + 14q  + 15q  + 13q  + 10q  + 6q  + 3q + 1

	o68 : ZZ[q]

We now turn to showing that the matroid _M_ is not in any of the classes of matroids for which Stanley's Conjecture was previously known to hold.

To see that _M_ is not paving we use the method `isPavingMatroid`.

	i69 : isPavingMatroid M

	o69 = false

Indeed _M_ is a rank seven matroid on ten elements with no coloops and has two circuits of size four.

	i70 : tally apply (M.orderedCircuits, C -> #C)

	o70 = Tally{4 => 2}
	            6 => 2
	            7 => 4

We can check that the last nonzero entry of the _h_-vector of _M_ is larger than five by inspecting the `matroidHPolynomial` of _M_.

	i71 : matroidHPolynomial M

	        7      6      5      4      3     2
	o71 = 6q  + 14q  + 15q  + 13q  + 10q  + 6q  + 3q + 1

	o71 : ZZ[q]

Next we want to see that the dual of _M_ is not a graphic matroid. One can do this either by inspecting the matrix `mat` above and finding a _U(2,4)_ minor or by using the test `isCographicMatroid`.

	i72 : isCographicMatroid M
	Isomorphism: matroids are equal
	Contract set {2, 3, 4, 6, 8}, delete set {4}

	o72 = false

It is well-known that a matroid is not transversal if it has as a minor the graphic matroid _G_ on _[3]_ with two edges between every pair of vertices. It's easy to see that the minor _N - \\{0,1,9}_ is isomorphic to _G_ as removing the corresponding columns f_ris in `_matand ` leaves us with the signed vertex-edge incidence matrix of _G_.

	i73 : mat_{3,4,5,6,7,8}

	o73 = | -1 -1 0  -1 -1 0  |
	      | 1  1  1  0  0  1  |
	      | 0  0  -1 1  1  -1 |

So _N_ is not transversal, as claimed.

Next we need to see that _N_ has at least _10 - 7 + 1 = 4_ parallel classes. This can be done either by inspection or by using the `parallelClasses` method.

	i74 : # parallelClasses N

	o74 = 6

Finally, since _M_ is a rank 7 matroid on 10 elements, it satisfies the remaining properties in the list. So we have shown that the class of internally perfect matroids constitutes a proper extension of the matroids for which Stanley's Conjecture is known to hold.






<!-- End Post -->
<!-- Links -->

[AHK]: https://arxiv.org/abs/1511.02888 "Hodge Theory for Combinatorial Geometries"
[BCC]: http://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/009PREPRINT.pdf "Broken Circuit Complexes: Factorizations and Generalizations, Bjorner and Ziegler"
[Birkner]: http://page.mi.fu-berlin.de/rbirkner/index.htm "Homepage"
[Chen]: https://math.berkeley.edu/people/grad/justin-chen "Homepage"
[DA]: https://arxiv.org/abs/1510.04532 "Internally Perfect Matroids"
[Depth]: http://www.math.uiuc.edu/Macaulay2/doc/Macaulay2-1.9.2/share/doc/Macaulay2/Depth/html/ "Finds the depth of a module or ideal, and systems of parameters in an ideal"
[HA]: http://www.math.uiuc.edu/Macaulay2/doc/Macaulay2-1.9.2/share/doc/Macaulay2/HyperplaneArrangements/html/ "a package for manipulating hyperplane arrangements"
[LV]: http://www.sciencedirect.com/science/article/pii/S0195669801904913 "Active Orders for Matroid Bases, Las Vergnas, 1980"
[Matroids]: https://github.com/jchen419/Matroids-M2 "A package for working with matroids in Macaulay2"
[M2]: http://www.math.uiuc.edu/Macaulay2/ "open source software system for computations in algebraic geometry and commutative algebra"
[MA]: https://github.com/aarondall/MatroidActivities-M2 "A package for working with ordered matroids in Macaulay2"
[OSA]: https://eudml.org/doc/142694 "Combinatorics and Topology of Complements of Hyperplanes, Orlik and Solomon, 1980"
[Pfeifle]: http://bgsmath.cat/fitxa-julian-pfeifle/ "Homepage"
[polymake]: https://polymake.org/doku.php "open source software for research in polyhedral geometry"
[Polyhedra]: http://www.math.uiuc.edu/Macaulay2/doc/Macaulay2-1.9.2/share/doc/Macaulay2/Polyhedra/html/ "for computations with convex polyhedra, cones, and fans"
[Posets]: http://www.math.uiuc.edu/Macaulay2/doc/Macaulay2-1.9.2/share/doc/Macaulay2/Posets/html/ "a package for working with partially ordered sets"
[SC]: http://www.math.uiuc.edu/Macaulay2/doc/Macaulay2-1.9.2/share/doc/Macaulay2/SimplicialComplexes/html/ "a package for manipulating simplicial complexes"
[ST]: http://www-math.mit.edu/~rstan/pubs/pubfiles/34.pdf "Cohen-Macaulay Complexes"
[intOrd]: MatroidActivities-M2/img/internalOrders/r7n10interestingExample.png "internal order of an interesting matroid of rank 7 on 10 elements"
<!-- TOC -->

[history]: #history
[the-package]: #the-package
[computing-with-matroids-in-matroidactivities]: #computing-with-matroids-in-matroidactivities
[algebraic-constructions-with-unordered-matroids]: #algebraic-constructions-with-unordered-matroids
[combinatorial-constructions-with-unordered-matroids]: #combinatorial-constructions-with-unordered-matroids
[tests-for-unordered-matroids]: #tests-for-unordered-matroids
[computing-with-ordered-matroids-in-matroidactivities]:#computing-with-ordered-matroids-in-matroidactivities
[algebraic-constructions-with-ordered-matroids]: #algebraic-constructions-with-ordered-matroids
[combinatorial-constructions-with-ordered-matroids]: #combinatorial-constructions-with-ordered-matroids
[tests-for-ordered-matroids]: #tests-for-ordered-matroids
[a-real-world-example]: #a-real-world-example
[proving-there-are-interesting-internally-perfect-matroids]: #proving-there-are-interesting-internally-perfect-matroids
[internally-perfect-matroids-and-stanleys-conjecture]: #internally-perfect-matroids-and-stanleys-conjecture
[stanleys-conjecture]: #stanleys-conjecture
[an-interesting-internally-perfect-matroid]: #an-interesting-internally-perfect-matroid
<!-- internal links -->

[i8]: #i8
[i17]: #i17
[i32]: #i32
<!-- Mouse over definitions -->

*[zonotopes]: affine projections of a cube
*[face ideal]: i.e., the Stanley-Reisner ideal of the independence complex
*[Cohen-Macaulay]: Krull dimension equals depth
*[broken circuit]: a subset of the ground set of an ordered matroid equal to an ordered circuit with its least element removed
<!--
tags:
Macaulay2
software
algebraic geometry
commutative algebra
polyhedral
subdivision
polytope
polytopal complex
polymake
Polyhedra
René Birkner
Julian Pfeifle
-->