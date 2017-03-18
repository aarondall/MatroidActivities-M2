# MatroidActivities-M2
A package for working with external and internal activities of ordered matroids in Macaulay2, it is the companion code to the article [Internally Perfect Matroids](https://arxiv.org/abs/1510.04532).

## Functionality
`MatroidActivities` provides basic methods for computing with activities in ordered matroids. The methods provided for ordered matroids are
* compute internal and external activities of arbitrary subsets of the ground set;
* compute the internal and external orders and obtain `Tikz` strings for them for easy insertion into `TeX` files; 
* determine if a matroid is internally perfect; and
* compute Björner's partition of the Boolean lattice induced by the ordered matroid.

## Installation
* First you will need a working version of `Macaulay2` (M2). Follow the instructions on the M2 [homepage](http://www.math.uiuc.edu/Macaulay2/) to download and install.
The source code for M2 is available on GitHub [here](https://github.com/Macaulay2/M2).

* The `MatroidActivities` package builds on and extends J. Chen's `Matroids` package for M2. So for `MatroidActivities` to work you will need to have `Matroids` installed. You can get the source code for that package [here](https://github.com/jchen419/Matroids-M2). Then simply add it to `/Macaulay2/code` and enter the following into any M2 interactive shell:

    ``i1: installPackage "Matroids"``
    
* Finally add `MatroidActivities.m2` to `/Macaulay2/code` and run
  
    ``i2: installPackage "MatroidActivities"``  
    ``i3: loadPackage "MatroidActivities"``
