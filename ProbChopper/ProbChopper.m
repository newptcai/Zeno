(* :Title: ProbChopper.m -- a package for probability theory *)

(* :Context: ProbChopper` *)

(* :Author: Xing Shi Cai *)

(* :Summary:
    A Mathematica package collecting basic probability theory results.
 *)

(* :Package Version: 0.1 *)

(* :Mathematica Version: 11.3 *)

(* :History:
   0.1 -- Add some Chernoff's inequalities for binomial distributions.
*)

(* :Keywords: probability, concentration inequalities, combinatorics. *)

(* set up the package context, including public imports *)

BeginPackage["ProbChopper`"]

(* usage messages for the exported functions and the context itself *)


ProbChopper::usage="ProbChopper.m is a Mathematica package collecting concentration inequalities, e.g., Chernoff's
bound, and some other simple results in probability theory. It is part of my collection of helper
functions for Mathematica called Zeno."

Chernoff::usage="Chernoff[n, p, a] \[GreaterEqual] Probability[Abs[x-n*p]>a, x\[Distributed]BinomialDistribution[n, p]].
Chernoff[n, p, a, Tail->\"Right\"] \[GreaterEqual] Probability[x-n*p>a, x\[Distributed]BinomialDistribution[n, p]].
Chernoff[n, p, a, Tail->\"Left\"] \[GreaterEqual] Probability[x-n*p<a, x\[Distributed]BinomialDistribution[n, p]].
Chernoff[n, p, a, Tail->\"Right\", Shifted->False] \[GreaterEqual] Probability[x>a, x\[Distributed]BinomialDistribution[n, p]].
Chernoff[n, p, a, Tail->\"Left\", Shifted->False] \[GreaterEqual] Probability[x<a, x\[Distributed]BinomialDistribution[n, p]].
Chernoff[n, p, a, \[Epsilon], Tail->\"Left\"] \[GreaterEqual] Probability[x>(1+a)n*p+\[Epsilon], x\[Distributed]BinomialDistribution[n, p]].
Chernoff[n, p, a, \[Epsilon], Tail->\"Right\"] \[GreaterEqual] Probability[x<(1-a)n*p-\[Epsilon], x\[Distributed]BinomialDistribution[n, p]].
An extra option Complexity->{1,2,3} can be used to choose the complexity of the returned bound.";

ChernoffPrintAll::usage="ChernoffPrintAll[] gives all the available Chernoff's bounds";
ChernoffPrint::usage="ChernoffPrint[complexity] gives all the available Chernoff's bounds of correpsonding complexity";

Tail::usage="Tail is an option for Chernoff bounds indicating whether we want to bound the \"Left\", \"Right\" or \"Both\" tails.";

Complexity::usage="Complexity is an option for Chernoff bounds indicating how complexity we want the bound to be. Choose in {1,2,3}.";

Shifted::usage="Tail is an option for Chernoff bounds indicating whether we are considering BinomialDistribution[n,p] shifted by its mean n*p.";


(* error messages for the exported objects *)

Chernoff::badcomplexity="The option complexity should be in {1,2,3} but `1` is given.";

(* options for exported functions *)

Options[Chernoff] = {Tail -> "Both", Shifted -> True, Complexity->1};

Begin["`Private`"]    (* begin the private context (implementation*part) *)

(* definition of auxiliary functions and local (static) variables *)

ChernoffBoundList = {Chernoff01, Chernoff02, Chernoff03};

ChernoffChooseComplexity[complexity_] := Module[{ChernoffX},
    ChernoffX = Quiet@ChernoffBoundList[[complexity]];
    If[MemberQ[ChernoffBoundList, ChernoffX], 
        Null,
        Message[Chernoff::badcomplexity, complexity];
        ChernoffX = Chernoff01
    ];
    ChernoffX
];

ChernoffInner[n_, p_, a_, eps_, bound_, tail_, shifted_] := Module[{d},
    Which[
        eps =!= 0, 
        d = a,
        shifted==False, 
        Which[
            tail=="Left", d=(n*p-a)/(n*p),
            tail=="Right", d=(a-n*p)/(n*p)
        ],
        True, d=a/(n*p)
    ];
    bound[n, p, d, eps, tail]
];

(* The following ones come from Graph Coloring and Probabilistic Methods. *)

(* A simpler version *)

Chernoff01[n_, p_, d_, eps_, "Right"] := (1 + d)^-eps E^(-(1/3) d^2 n p);

Chernoff01[n_, p_, d_, eps_, "Left"] := (1 - d)^eps E^(-(1/3) d^2 n p);

Chernoff01[args__, "Both"] := Chernoff01[args, "Left"]+Chernoff01[args, "Right"];

(* A most complicated version *)

Chernoff02[n_, p_, d_, eps_, "Left"]:=E^(-(1/2) (d+0/(n p))^2 n p + 1/2 (d+0/(n p))^3 n p)/(1 + d)^eps;

Chernoff02[n_, p_, d_, eps_, "Right"]:=E^(-(1/2) (d+0/(n p))^2 n p + 1/2 (d+0/(n p))^3 n p)*(1 - d)^eps;

Chernoff02[args__, "Both"] := Chernoff02[args, "Left"]+Chernoff02[args, "Right"];

(* A more complicated version *)

Chernoff03[n_, p_, d_, eps_, "Right"] := (E^d/(1 + d)^(1 + d))^(n*p)/(1 + d)^eps;

Chernoff03[n_, p_, d_, eps_, "Left"] := (E^(-d)/(1 - d)^(1 - d))^(n*p)*(1 - d)^eps;

Chernoff03[args__, "Both"] := Chernoff03[args, "Left"]+Chernoff03[args, "Right"];

ChernoffPrint[complexity_:1]:=Module[{lhs, rhs, n, p, a, \[Epsilon], x, X},
    n = Symbol["n"];
    a = Symbol["a"];
    p = Symbol["p"];
    \[Epsilon] = Symbol["\\[Epsilon]"];
    x=Symbol["x"];
    X=Symbol["X"];
    lhs={
        Chernoff[n, p, a, Complexity->complexity],
        Chernoff[n, p, a, Tail -> "Right", Complexity->complexity],
        Chernoff[n, p, a, Tail -> "Left"],
        Chernoff[n, p, a, Tail -> "Right", Shifted -> False, Complexity->complexity],
        Chernoff[n, p, a, Tail -> "Left", Shifted -> False, Complexity->complexity],
        Chernoff[n, p, a, \[Epsilon], Tail -> "Left", Complexity->complexity],
        Chernoff[n, p, a, \[Epsilon], Tail -> "Right", Complexity->complexity]
    };
    rhs=Inactivate[{
        Probability[Abs[x-n*p]>a, x\[Distributed]X],
        Probability[x-n*p>a, x\[Distributed]X],
        Probability[x-n*p<a, x\[Distributed]X],
        Probability[x>a, x\[Distributed]X],
        Probability[x<a, x\[Distributed]X],
        Probability[x>(1+a)n*p+\[Epsilon], x\[Distributed]X],
        Probability[x<(1-a)n*p-\[Epsilon], x\[Distributed]X]
    }, Probability];
    Print["X=BinomialDistribution[n, p]"];
    Print[StringForm["Complexity=`1`", complexity]];
    MapThread[Print[#2<=#1]&, {lhs, rhs}];
];

(* definition of the exported functions *)

Chernoff[n_, p_, a_, Shortest[eps_:0], opt:OptionsPattern[]] := Module[{ChernoffX, complexity},
    complexity = OptionValue[Complexity];
    ChernoffX = ChernoffChooseComplexity[complexity];
    ChernoffInner[n, p, a, eps, ChernoffX, OptionValue[Tail], OptionValue[Shifted]]
];

ChernoffPrintAll[]:=Module[{},
    Table[ChernoffPrint[complexity], {complexity,1,3}];
];

(* end the private context *)

End[ ]

(* end the package context *)

EndPackage[ ]
