# MatroidActivities-M2
A package originally made for working with external and internal activities of ordered matroids in Macaulay2, it is the companion code to the article [Internally Perfect Matroids](https://arxiv.org/abs/1510.04532). It now includes a number of methods for working with unordered matroids.

## Functionality
Version 0.2 of `MatroidActivities` greatly expands on Version 0.1. There are new methods for computing with both matroids and ordered matroids. The new functionality includes:

 + Methods for constructing a(n ordered) matroid from an ideal, simplicial complex, or central arrangement;
 + Methods for constructing the face ring, Chow ring, and Orlik-Solomon algebra of a matroid or ordered matroid;
 + Testing if a matroid is simple, binary, ternary, (co)graphic, regular, or paving;
 + TikZ rendering of the internal order and the external order split into two methods for improved visualization.

## Resources
There are three resources for learning to use this package; the first two provided by the author and the third by the user. Every method in the package is documented and an attempt was made to make this documentation reasonably thorough. Moreover, an [introductory session](https://github.com/aarondall/MatroidActivities-M2/blob/master/introductorySession.md) is available as a guide to this package. Finally, and probably most importantly, is the user's curiosity about, and need for, such software.

## Installation
* First you will need a working version of `Macaulay2` (M2). Follow the instructions on the M2 [homepage](http://www.math.uiuc.edu/Macaulay2/) to download and install.
The source code for M2 is available on GitHub [here](https://github.com/Macaulay2/M2).

* The `MatroidActivities` package builds on and extends J. Chen's `Matroids` package for M2. So for `MatroidActivities` to work you will need to have `Matroids` installed. You can get the source code for that package [here](https://github.com/jchen419/Matroids-M2). Then simply add it to `/Macaulay2/code` and enter the following into any M2 interactive shell:

    ``i1: installPackage "Matroids"``

* Finally add `MatroidActivities.m2` to `/Macaulay2/code` and run

    ``i2: installPackage "MatroidActivities"``
    ``i3: loadPackage "MatroidActivities"``
