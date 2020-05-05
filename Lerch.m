(* ::Package:: *)

(* ::Title:: *)
(*Lerch.m -- Asymptoic expansion for Lerch Zeta functions. *)


(* :Context: Lerch` *)

(* :Author: Xing Shi Cai *)

(* :Package Version: 0.1.0 *)

(* :Mathematica Version: 12.1 *)

(* :History:
*)

(* :Keywords: expression manipulation, helper functions. *)


BeginPackage["Lerch`"]

Unprotect["Lerch`*"];
ClearAll["Lerch`*"];
ClearAll["Lerch`Private`*"];

(* usage messages for the exported functions and the context itself *)

LerchPhiSeries::usage="LerchPhi[z, s, a, n] gives the n-th order series expansion of LerchPhi[z, s, a] as a goes to inifnity"

LerchPhiExpand::usage="Expand LerchPhi[z, s, a] as a goes to inifnity"

LerchPhiSum::usage="Expand Sum[z^n/n^s, {n, 1, m}] as m goes to inifnity"

Begin["`Private`"]    (* begin the private context (implementation*part) *)


(* ::Chapter:: *)
(* Expansion *)

c[0, z_]:= 1/(1-z)
c[n_, z_]:=(-1)^n PolyLog[-n, z]/n!

LerchPhiSeries[z_, s_, a_, n_] := Sum[c[n0, z] Pochhammer[s, n0]/a^(n0+s), {n0, 0, n-1}]

LerchPhiExpand[expr_, n_] := expr /. LerchPhi[z_, s_, a_] -> LerchPhiSeries[z, s, a, n]

LerchPhiSum[expr_, n_] := expr /. \
    Inactive[Sum][Times[Power[j_,-s_.],Power[z_,j_]],List[j_,1,m_-1]] \
    ->PolyLog[s,z]-z^m/m^s * Sum[c[n0, z] Pochhammer[s, n0]/m^n0, {n0, 0, n-1}]


(* end the private context *)
End[ ]

Protect["Lerch`*"];


(* end the package context *)
EndPackage[];
