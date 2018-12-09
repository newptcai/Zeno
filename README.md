# Zeno -- a collection of helper functions for symbolic computations in Mathematica

## Purpose of the project

In my [recent research](http://www2.math.uu.se/~xinca341/pages/publications.html), I found that I
often have to manipulate large symbolic expressions. Sometimes these equations are even hard to copy
by hand on paper. Using Mathematica helped a lot. It provides many powerful features
for manipulate symbolic expressions--when I do not know how to transform an expression through
programming, at least I can copy-paste it and change it manually.

Zeno is a collection of helper functions that I wrote the past few months. Usually they are just
wrappers for one-line codes. But I gradually learned to write them in better and more conciser ways,
thanks to many helps that I got from
[mathematica.stackexchange.com](https://mathematica.stackexchange.com).  Hopefully these will also
be helpful for others. At least by checking the code, you will see how to do certain things in Mathematica.

Zeno currently contains these packages:

* `ChernoffBound.m` -- concentration inequalities.
* `CalcMoment.m` -- formulas for calculating moments of random variables.

(The project is named after the accent Greek philosopher [Zeno of
Citium](https://en.wikipedia.org/wiki/Zeno_of_Citium).)


## Usage

Currently these packages do not have dependency. So you can simply download a package, say
`CalcMoment.m`, in either the same folder as your Mathematica notebook and load it by

    SetDirectory[NotebookDirectory[]];
    Needs["CalcMoment`"]

You can also put it in `FileNameJoin@{$UserBaseDirectory, "Applications"}` and then load it in your notebook by

    Needs["CalcMoment`"]

To see available functions, type

    ?CalcMoment`*

Check this [test notebook](Zeno-test.nb) for examples of how to use these packages.

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

In Patrice, it can be convenient to write E(Y[Y &lt; a]) in terms of the left and right tails of
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
