(* :Title: CalcMoment.m -- formulas or computing moments of random variables *)

(* :Context: CalcMoment` *)

(* :Author: Xing Shi Cai *)

(* :Package Version: 0.1 *)

(* :Mathematica Version: 11.3 *)

(* :History:
*)

(* :Keywords: probability, concentration inequalities, combinatorics. *)

(* set up the package context, including public imports *)

BeginPackage["CalcMoment`"]

(* usage messages for the exported functions and the context itself *)

CalcMoment::usage="CalcMoment.m is a Mathematica package collecting \
some formulas of computing moments of random variables. It is part of my collection \
of helper functions for probability theory called PropChopper. Note all returned expressions are unevaluated."

TruncatedExpMoment::usage="TruncatedExpMoment[dist,a] gives Expectation[E^-Y \
ind[Y<a],Y\[Distributed]dist]. The option MomentForm taking values in {\"Basic\", \
\"Left\", \"Right\"} controls whether the result is given in its basic form, or \
in terms of the right or left tails of Y."

TruncatedMoment::usage="TruncatedMoment[dist, p, a] gives Expectation[Y^p \
If[Y<a, 1, 0],Y\[Distributed]dist] for a random variable Y>=0. The option MomentForm taking values in {\"Basic\", \
\"Left\", \"Right\"} controls whether the result is given in its basic form, or \
in terms of the right or left tails of Y."

MomentForm::usage="The option MomentForm taking values in {\"Basic\", \
\"Left\", \"Right\"} controls whether the moment of a random variable Y is given in its basic form, or \
in terms of the right or left tails of Y.";

(* error messages for the exported objects *)

(* options for exported functions *)

Options[TruncatedMoment] = {MomentForm};

Options[TruncatedExpMoment] = {MomentForm};

Begin["`Private`"]    (* begin the private context (implementation*part) *)

(* definition of auxiliary functions and local (static) variables *)

TruncatedMoment[dist_, moment_, truncate_]:=TruncatedMoment[dist, moment, truncate, MomentForm->"Basic"];
TruncatedMoment[dist_, moment_, truncate_, MomentForm->"Basic"] := Module[
    {p, a, Y},
    p = moment;
    a = truncate;
    Y = Symbol["Y"];
    Inactive[Expectation][If[Y<a, 1, 0] Y^p, Distributed[Y, dist]]
];

TruncatedMoment[dist_, moment_, truncate_, MomentForm->"Right"] := Module[
    {p, a, Y, y}, 
    p = moment;
    a = truncate;
    Y = Symbol["Y"];
    y = Symbol["y"];
    Inactivate[Integrate[p*y^(p - 1)*Probability[Y > y, Distributed[Y, dist]], {y, 0, a}]-a^p Probability[Y>a, Distributed[Y,dist]], Integrate|Probability]
];

TruncatedMoment[dist_, moment_, truncate_, MomentForm->"Left"] := Module[
    {p, a, Y, y}, 
    p = moment;
    a = truncate;
    Y = Symbol["Y"];
    y = Symbol["y"];
    Inactivate[a^p Probability[Y<a, Distributed[Y,dist]]-Integrate[p*y^(p - 1)*Probability[Y < y, Distributed[Y, dist]], {y, 0, truncate}], Integrate|Probability]
];


TruncatedExpMoment[dist_, truncate_]:=TruncatedExpMoment[dist, truncate, MomentForm->"Basic"];
TruncatedExpMoment[dist_, truncate_, MomentForm->"Basic"]:=Module[
    {Y},
    Y = Symbol["Y"];
    Inactive[Expectation][If[Y<truncate, 1, 0] E^-Y, Distributed[Y, dist]]
];

TruncatedExpMoment[dist_, a_, MomentForm->"Left"] := Module[
    {Y, y}, 
    Y = Symbol["Y"];
    y = Symbol["y"];
    Inactivate[Probability[Y<a,Y\[Distributed]dist]/E^a+Integrate[Probability[Y<y,Y\[Distributed]dist]/E^y,{y,0,a}], Integrate|Probability]
];

TruncatedExpMoment[dist_, a_, MomentForm->"Right"]:=Module[
    {Y, y}, 
    Y = Symbol["Y"];
    y = Symbol["y"];
    Inactivate[1-Probability[Y>a,Y\[Distributed]dist]/E^a-Integrate[Probability[Y>y,Y\[Distributed]dist]/E^y,{y,0,a}], Integrate|Probability]
];

(* end the private context *)

End[ ]

(* end the package context *)

EndPackage[ ]
