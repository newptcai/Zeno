(* :Title: ChernoffBound.m -- a package for Chernoff bounds *)

(* :Context: ChernoffBound *)

(* :Author: Xing Shi Cai *)

(* :Summary:
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
An extra option Complexity->{1,2,3} can be used to choose the complexity of the returned bound."

(* error messages for the exported objects *)

Chernoff::badcomplexity="The option complexity should be in {1,2,3} but `1` is given."

(* options for exported functions *)

Options[Chernoff] = {Tail -> "Both", Shifted -> True, Complexity->1}

Begin["`Private`"]    (* begin the private context (implementation*part) *)

(* definition of auxiliary functions and local (static) variables *)

ChernoffBoundList = {Chernoff01, Chernoff02, Chernoff03};

Map[(Options[#] = {Tail -> "Both", Shifted -> True})&, ChernoffBoundList];


ChernoffChooseComplexity[complexity_] := Module[{ChernoffX},
    ChernoffX = Quiet@ChernoffBoundList[[complexity]];
    If[MemberQ[ChernoffBoundList, ChernoffX], 
        Null,
        Message[Chernoff::badcomplexity, complexity];
        ChernoffX = Chernoff01
    ];
    ChernoffX
];

(* The following ones come from Graph Coloring and Probabilistic Methods. *)

(* A simpler version *)

Chernoff01ShiftAbs[n_, p_, a_]:=2 Exp[-(a^2/(3 n*p))];

Chenorff01MultRight[n_, p_, d_, eps_:0] := (1 + d)^-eps E^(-(1/3) d^2 n p);

Chenorff01MultLeft[n_, p_, d_, eps_:0] := (1 - d)^eps E^(-(1/3) d^2 n p);

(* Shortest[] is used to avoid conflicts of optional eps and options *)
Chernoff01[n_, p_, a_, Shortest[eps_:0], opt:OptionsPattern[]] := Module[{tail, shifted},
    tail=OptionValue[Tail];
    shifted=OptionValue[Shifted];
    Which[
        eps =!= 0, 
        Which[
            tail=="Left", Chenorff01MultLeft[n, p, a, eps],
            tail=="Right", Chenorff01MultRight[n, p, a, eps]
        ],
        shifted==False, 
        Which[
            tail=="Left", Chernoff01[n, p, n*p-a, Tail->tail],
            tail=="Right", Chernoff01[n, p, a-n*p, Tail->tail]
        ],
        True,
        If[
            tail=="Both", 
            Chernoff01ShiftAbs[n, p, a],
            1/2 * Chernoff01ShiftAbs[n, p, a]
        ]
    ]
];

(* A more complicated version *)

Chernoff02ShiftAbs[n_, p_, a_]:=2 Exp[-((1+a/(n*p))Log[1+a/(n*p)]-a/(n*p))n*p];

Chenorff02MultRight[n_, p_, d_, eps_:0] := (E^d/(1 + d)^(1 + d))^(n*p)/(1 + d)^eps;

Chenorff02MultLeft[n_, p_, d_, eps_:0] := (E^(-d)/(1 - d)^(1 - d))^(n*p)*(1 - d)^eps;

(* Shortest[] is used to avoid conflicts of optional eps and options *)
Chernoff02[n_, p_, a_, Shortest[eps_:0], opt:OptionsPattern[]] := Module[{tail, shifted},
    tail=OptionValue[Tail];
    shifted=OptionValue[Shifted];
    Which[
        eps =!= 0, 
        Which[
            tail=="Left", Chenorff02MultLeft[n, p, a, eps],
            tail=="Right", Chenorff02MultRight[n, p, a, eps]
        ],
        shifted==False, 
        Which[
            tail=="Left", Chernoff02[n, p, n*p-a, Tail->tail],
            tail=="Right", Chernoff02[n, p, a-n*p, Tail->tail]
        ],
        True,
        If[
            tail=="Both", 
            Chernoff02ShiftAbs[n, p, a],
            1/2 * Chernoff02ShiftAbs[n, p, a]
        ]
    ]
];

Chernoff03[]:=Null;


(* A more complicated version *)

Binom03ShiftRight[n_, p_, a_]:=Exp[-(a^2/(2 n*p))+a^3/(2(n*p)^3)];

(* Multiplicative form.  *)


(* definition of the exported functions *)

Chernoff[n_, p_, a_, Shortest[eps_:0], opt:OptionsPattern[]] := Module[{ChernoffX, complexity},
    complexity = OptionValue[Complexity];
    ChernoffX = ChernoffChooseComplexity[complexity];
    ChernoffX[n, p, a, eps, FilterRules[{opt},Options[ChernoffX]]]
];

(* end the private context *)

End[ ]

(* end the package context *)

EndPackage[ ]
