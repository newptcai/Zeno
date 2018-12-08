# ProbChopper -- A Mathematica package for some basic probability theory

`ProbChopper.m` is a Mathematica package collecting concentration inequalities, e.g., Chernoff's
bound, and some other simple results in probability theory. It is part of my collection of helper
functions for Mathematica called Zeno.

## Usage

You can put the file `ProbChopper.m` in either the same folder as your Mathematica notebook 
and load it by

    SetDirectory[NotebookDirectory[]];
    Needs["ProbChopper`"]

You can also put it in `FileNameJoin@{$UserBaseDirectory, "Applications"}` and then load it in your notebook by

    Needs["ProbChopper`"]

To see available functions, type

    ?ProbChopper`*

## Chernoff's bounds

Chernoff's bounds are some concentration inequalities widely used in probabilistic combinatorics.
`ProbChopper.m` includes several versions of Chernoff's bounds for binomial distributions.
To see all available inequalities available, type

    ChernoffPrintAll[]

The proofs of these inequalities can be found in 

1. Michael Molloy and Bruce Reed, Graph Coloring and Probabilistic Methods, Springer Science & Business Media, 29 Jun 2013.

2. Michael Mitzenmacher, Eli Upfal, Probability and Computing: Randomized Algorithms and Probabilistic Analysis, Cambridge University Press, 31 Jan 2005.

3. Noga Alon, Joel H. Spencer, The Probabilistic Method, 2nd ed., John Wiley & Sons, 5 Apr 2004.

4. Wikipedia -- [Chernoff Bound](https://en.wikipedia.org/wiki/Chernoff_bound)
