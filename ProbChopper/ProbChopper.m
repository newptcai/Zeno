(* :Title: ProbChopper.m -- some basic results in probability theory *)

(* :Context: ProbChopper` *)

(* :Author: Xing Shi Cai *)

(* :Requirement:
    - ChernoffBound.m
    - CalcMoment.m
 *)

(* :Package Version: 0.1 *)

(* :Mathematica Version: 11.3 *)

(* :History:
*)

(* :Keywords: probability, concentration inequalities, combinatorics. *)

(* set up the package context, including public imports *)

BeginPackage["ProbChopper`", {"ChernoffBound`", "CalcMoment`"}]

(* usage messages for the exported functions and the context itself *)


ProbChopper::usage="ProbChopper.m is a Mathematica package collecting \
concentration inequalities, e.g., Chernoff's bound, and some other simple \
results in probability theory. It is part of my collection of helper functions \
for Mathematica called Zeno."

(* error messages for the exported objects *)

(* options for exported functions *)

Begin["`Private`"]    (* begin the private context (implementation*part) *)

(* definition of auxiliary functions and local (static) variables *)

(* definition of the exported functions *)

(* end the private context *)

End[ ]

(* end the package context *)

EndPackage[ ]
