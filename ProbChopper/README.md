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

The package contains some sub-packages, which can be used independently:

* `ChernoffBound.m` -- concentration inequalities.
* `CalcMoment.m` -- formulas for calculating moments of random variables.

## `ChernoffBound.m` -- Chernoff's bounds

Chernoff's bounds are some concentration inequalities widely used in probabilistic combinatorics.
`ProbChopper.m` includes several versions of Chernoff's bounds for binomial distributions.
To see all available inequalities available, type

    ChernoffPrintAll[]

The proofs of these inequalities can be found in 

1. Michael Molloy and Bruce Reed, Graph Coloring and Probabilistic Methods, Springer Science & Business Media, 29 Jun 2013.

2. Michael Mitzenmacher, Eli Upfal, Probability and Computing: Randomized Algorithms and Probabilistic Analysis, Cambridge University Press, 31 Jan 2005.

3. Noga Alon, Joel H. Spencer, The Probabilistic Method, 2nd ed., John Wiley & Sons, 5 Apr 2004.

4. Wikipedia -- [Chernoff Bound](https://en.wikipedia.org/wiki/Chernoff_bound)

## `CalcMoment.m` -- Truncated Moments

Given a random variable Y, sometimes we want to compute the expectation of Y[Y &lt; a], where
[P]=1 if the P and true and [P]=0 if P is false. (The notation is called [Iverson
Bracket](https://en.wikipedia.org/wiki/Iverson_bracket).) 

In Patrice, it can be convenient to write $\mathbb E(Y[Y \le a])$ in terms of the left and right tails of
$Y$.  These are two function `TruncatedMoment` and `TruncatedExpMoment` contained in `CalcMoment.m` which does this. 
You can load it and try it in a Mathematica notebook like this

```mathematica
SetDirectory[NotebookDirectory[]];
Get["CalcMoment`"]

gdist = GammaDistribution[3, 7]
gtest = TruncatedMoment[gdist, p, a] == TruncatedMoment[gdist, p, a, MomentForm -> "Left"] == TruncatedMoment[gdist, p, a, MomentForm -> "Right"]
Assuming[0 < a && p >= 1, gtest // Activate // FullSimplify]

edist = ExponentialDistribution[1]
etest = TruncatedExpMoment[edist, a] == TruncatedExpMoment[edist, a, MomentForm -> "Left"] == TruncatedExpMoment[edist, a, MomentForm -> "Right"]
Assuming[0 < a, etest // Activate // FullSimplify]
```
