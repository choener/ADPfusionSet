[![Build Status](https://travis-ci.org/choener/ADPfusionSet.svg?branch=master)](https://travis-ci.org/choener/ADPfusionSet)

# ADPfusionSet

[*generalized Algebraic Dynamic Programming Homepage*](http://www.bioinf.uni-leipzig.de/Software/gADP/)

Ideas implemented here are described in a couple of papers:



1.  Christian Hoener zu Siederdissen  
    *Sneaking Around ConcatMap: Efficient Combinators for Dynamic Programming*  
    2012, Proceedings of the 17th ACM SIGPLAN international conference on Functional programming  
    [paper](http://doi.acm.org/10.1145/2364527.2364559) [preprint](http://www.tbi.univie.ac.at/newpapers/pdfs/TBI-p-2012-2.pdf)  
1.  Andrew Farmer, Christian Höner zu Siederdissen, and Andy Gill.  
    *The HERMIT in the stream: fusing stream fusion’s concatMap*  
    2014, Proceedings of the ACM SIGPLAN 2014 workshop on Partial evaluation and program manipulation.  
    [paper](http://dl.acm.org/citation.cfm?doid=2543728.2543736)  
1.  Christian Höner zu Siederdissen, Ivo L. Hofacker, and Peter F. Stadler.  
    *Product Grammars for Alignment and Folding*  
    2014, IEEE/ACM Transactions on Computational Biology and Bioinformatics. 99  
    [paper](http://ieeexplore.ieee.org/xpl/articleDetails.jsp?arnumber=6819790)  
1.  Christian Höner zu Siederdissen, Sonja J. Prohaska, and Peter F. Stadler  
    *Algebraic Dynamic Programming over General Data Structures*  
    2015, BMC Bioinformatics  
    [preprint](http://www.bioinf.uni-leipzig.de/Software/gADP/preprints/hoe-pro-2015.pdf)  
1.  Maik Riechert, Christian Höner zu Siederdissen, and Peter F. Stadler  
    *Algebraic dynamic programming for multiple context-free languages*  
    2015, submitted  
    [preprint](http://www.bioinf.uni-leipzig.de/Software/gADP/preprints/rie-hoe-2015.pdf)  



# Introduction

ADPfusionSet extends ADPfusion with index structures suitable for sets.
Included are sets, and sets with one and two boundaries. The classical example
for DP on sets with a single boundary is the travelling salesman problem. Here,
the set denotes the set of cities already visited, while the boundary is the
last city that was visited.



# Installation

Follow the [gADP examples](http://www.bioinf.uni-leipzig.de/Software/gADP/index.html).



#### Contact

Christian Hoener zu Siederdissen  
Leipzig University, Leipzig, Germany  
choener@bioinf.uni-leipzig.de  
<http://www.bioinf.uni-leipzig.de/~choener/>  

