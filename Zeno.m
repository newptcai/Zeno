(* ::Package:: *)

(* ::Title:: *)
(*Zeno.m -- helper functions for manipulate symbolic equations*)


(* :Context: Zeno` *)

(* :Author: Xing Shi Cai *)

(* :Package Version: 0.1 *)

(* :Mathematica Version: 11.3 *)

(* :History:
*)

(* :Keywords: expression manipulation, helper functions. *)


BeginPackage["Zeno`"]

(* usage messages for the exported functions and the context itself *)

Const0::usage="Represent a positive constant"

MyAssumptions::usage="MyAssumptions replaces $Assumptions in each individual notebook. So in effect, each notebook has it own $Assumptions."

BigO::usage="BigO[f[x]] denote an implicit function g[x] that satisfies |g[x]|<C f[x].";
PowerToBigO::usage="PowerToBigO[expr, m, expo] turns expr to BigO[b m^a] if expr=b*m^a and a<=expo";
BigO2Zero::usage="BigO2Zero[expr] turns all BigO terms in expr to 0.";
ExpandBigO::usage="ExpandBigO[expr] turns all BigO[a] terms in expr to BigO[Expand[a]].";
BigO2Const::usage="BigO2Const[expr] turns all BigO[a] terms in expr to Const0*a.";
smallo::usage="smallo[f[x]] denote an implicit function g[x] that satisfies |g[x]/f[x]| -> 0 as x -> Infinity.";

PowerTosmallo::usage="PowerTosmallo[expr, m, expo] turns expr to smallo[b m^a] if expr=b*m^a and a<=expo";
smallo2Zero::usage="smallo2Zero[expr] turns all smallo terms in expr to 0.";
Expandsmallo::usage="Expandsmallo[expr] turns all smallo[a] terms in expr to smallo[Expand[a]].";
smallo2Const::usage="smallo2Const[expr] turns all smallo[a] terms in expr to Const0*a.";

SimplifyTerms::usage="SimplifyTerms[expr] simplify each term in expr separately";

InactivateAll::usage="InactivateAll[expr] applies Inactivate to all heads in expr except head in {Plus,Power,Times}.
InactivateAll[expr,heads] applies Inactivate to all heads in expr except head in {Plus,Power,Times} or in heads.
InactivateAll[expr,h] applies Inactivate to all heads in expr except head in {Plus,Power,Times, h}.";

FactorOut::usage="FactorOut[expr, fact] turns (a + fact b) in expr to fact(a/fact + b)";
BringOut::usage="BringOut[expr, head] take constant factors in a out of head[a, {i, c, d}] repeatedly until no such factor exists anymore."
BringOutSum::usage="BringOut[expr, head] take constant factors in a out of Sum[a, {i, c, d}] repeatedly until no such factor exists anymore."
BringOutInt::usage="BringOut[expr, head] take constant factors in a out of Integrate[a, {i, c, d}] repeatedly until no such factor exists anymore."

KeepOnly::usage="KeepOnly[expr, keep] turns all h1[a*h2[keep], b] in expr into a*h1[h2[keep],b] until it is not possible to do so anymore."

iSum::usage="iSum is a shorthand for Inactive[Sum]";
iInd::usage="iInd is a shorthand for Inactive[Ind]";
iInt::usage="iInt is a shorthand for Inactive[Integrate]";
iLog::usage="iLog is a shorthand for Inactive[Log]";
iLg::usage="iLg is a shorthand for Inactive[Lg]";
iFracPart::usage="iFracPart is a shorthand for Inactive[FracPart].";

ExpandHead::usage="ExpandHead[expr, h] applies Expand to the first variable for all heads h in expr.";
SplitHead::usage="SplitHead[expr, f] split every f[a+b] in expr to f[a]+f[b].
SplitHead[expr, {f1,f2,...,fk}] split every fi[a+b] in expr to fi[a]+fi[b], for i=1...k sequentially";
SwitchHead::usage="SwitchHead[expr,h1,h2] switch the position of h1 and h2 in expr.";

SplitIndex::usage="SplitIndex[expr, head, s, g] turns head[a, {x, l, u}] in expr \
into head[a,{x,l,s}]~g~head[a,{x,s+1,u}]";

ShiftHead::usage="ShiftHead[expr, head, shift] turns head[f[i],{i, a, b}] in expr \
into head[f[i+shift], {i, a-shift, b-shift}]"

TruncateHead::usage="TruncateHead[expr, head, upper] turns head[a, {i, l, u}] in expr \
into head[a, {i, l, upper}]";

MergeHead::usage="MergeHead[expr, head] turns head[a1, b]+head[a2,b] in expr \
into head[a1+a2,b]."

TriAbs::usage="TriAbs[expr,c] turns Abs[a-b] in expr to Abs[a-c]+Abs[c-b]";

ToLeft::usage="ToLeft[ieq] moves all terms of the inequality ieq to one left-hand-side."
ToRight::usage="ToRight[ieq] moves all terms of the inequality ieq to one right-hand-side."

SplitInequality::usage="SplitInequality[expr,a,split,ieq] turns ieq[a, c] in expr to ieq[a,split] || ieq[split,a,c]."
SplitGreater::usage="SplitGreater[expr,a,split,ieq] turns a>c in expr to a>c || split>a>c."
SplitLess::usage="SplitLess[expr,a,split,ieq] turns a<c in expr to a<c || split<a<c."

ReducePositive::usage="ReducePositive[expr, vars] reduces the statement expr by \
solving equations or inequalities for vars and eliminating quantifiers, \
assuming that all parameters in expr except vars are positive real numbers."

Lg::usage="Lg[x] is a shorthand for Log[2,x]";
Ind::usage="Ind[cond]==1 if cond is True. Otherwise Ind[cond]==0.";

FracPart::usage="FracPart[x] is the fractional part of x, i.e., FracPart[x]==x-Floor[x]. Note this different from the system function FractionalPart if x<0.";
Floor2Frac::usage="Floor2Frac[expr] turns Floor[x] in expr to x-FracPart[x]."
UpperFloor::usage="UpperFloor[expr] turns Floor[x] in expr to x."
LowerFloor::usage="LowerFloor[expr] turns Floor[x] in expr to x-1."

BringOutE::usage="BringOutE[expr, terms] take all members of terms and constants out of \
\[DoubleStruckCapitalE][a]";

\[DoubleStruckCapitalE]::usage="\[DoubleStruckCapitalE][x] stands for the expectation of x. \
It does not do any computation.";

\[DoubleStruckCapitalP]::usage="\[DoubleStruckCapitalP][x] stands for the probability of x. \
It does not do any computation.";

ExpandSum::usage="ExpandSum[expr] applies Expand to all summands of Sum in expr."

ShiftSum::usage="ShiftSum[expr, shift] turns Sum[f[i],{i, a, b}] in expr \
into Sum[f[i+shift], {i, a-shift, b-shift}]."

PrependSum::usage="PrependSum[expr, shift] turns Sum[f[i],{i, a, b}] in expr \
into Sum[f[i], {i, a-shift, b-shift}]-Sum[f[i], {i, a-shift, a-1}]."

SplitSumIndex::usage="SplitSumIndex[expr, s] turns Sum[a, {x, l, u}] in expr \
into Sum[a,{x,l,s}]+Sum[a,{x,s+1,u}].";

SwitchIntSum::usage="SwitchIntSum[expr] turns Integrate[Sum[a[x,i],{i, l0, u0}], {x,l1,u1}] \
in expri into Sum[Integrate[a[x,i],{x,l1,u1}], {i, l0, u0}]."

SwitchSumInt::usage="SwitchSumInt[expr] turns Sum[Integrate[a[x,i],{x,l1,u1}], {i, l0, u0}] \
in expri into Integrate[Sum[a[x,i],{i, l0, u0}], {x,l1,u1}]."

SplitSum::usage="SplitSum[expr] turns Sum[a+b,c] in expr into Sum[a,c]+Sum[b,c]."

TruncateSum::usage="TruncateSum[expr, upper] turns Sum[a, {i, l, u}] in expr \
into Sum[a, {i, l, upper}]";

MergeSum::usage="MergeSum[expr, head] turns Sum[a1, b]+Sum[a2,b] in expr \
into Sum[a1+a2,b]."

Begin["`Private`"]    (* begin the private context (implementation*part) *)


(* ::Chapter:: *)
(*Assumptions*)


MyAssumptions={k\[Element]Integers,k>=0,
m\[Element]Integers,m>=0,
n\[Element]Integers,n>=0,
l\[Element]Integers,l>=0,
Const0>0
};

$Assumptions:=ToExpression["MyAssumptions"];


(* ::Chapter:: *)
(*Asymptotics*)


(* ::Subchapter:: *)
(*BigO notation*)


PowerToBigO[expr_,m_,expo_]:=With[{mexpo=Exponent[expr,m]}, If[Simplify[mexpo<=expo],BigO[m^mexpo]*expr/m^mexpo,expr,expr]];
BigO2Zero[expr_]:=expr/.BigO[_]:>0;
ExpandBigO[expr_]:=ExpandHead[expr,BigO];
BigO2Const[expr_]:=expr/.BigO[a_]->Const0 a;

BigO[0]=0;
BigO[x_]/;NumberQ[x]:=BigO[1];
BigO/:BigO[x_]+BigO[y_]:=BigO[x+y];
BigO/:BigO[x_]-BigO[y_]:=BigO[x+y];
BigO/:y_*BigO[x_]:=BigO[x*y];
BigO/:BigO[x_+BigO[y_]]:=BigO[x+y];
BigO/:BigO[x_+smallo[y_]]:=BigO[x]+smallo[y];
BigO/:BigO[x_*y_]/;NumberQ[x]:=BigO[y];
BigO/:BigO[y_]*BigO[x_]:=BigO[x*y];
BigO/:BigO[y_]^p_:=BigO[y^p];
BigO/:Limit[BigO[x_],y__]:=BigO[Limit[x,y]]

BigO/:MakeBoxes[BigO,TraditionalForm]:="O"


(* ::Subchapter:: *)
(*smallo notation*)


PowerTosmallo[expr_,m_,expo_]:=With[{mexpo=Exponent[expr,m]}, If[Simplify[mexpo<=expo],smallo[m^mexpo]*expr/m^mexpo,expr,expr]];
smallo2Zero[expr_]:=expr/.smallo[_]:>0;
Expandsmallo[expr_]:=ExpandHead[expr,smallo];
smallo2Const[expr_]:=expr/.smallo[a_]->Const0 a;

smallo[0]=0;
smallo[x_]/;NumberQ[x]:=smallo[1];
smallo/:smallo[x_]+smallo[y_]:=smallo[x+y];
smallo/:smallo[x_]-smallo[y_]:=smallo[x+y];
smallo/:y_*smallo[x_]:=smallo[x*y];
smallo/:smallo[x_+smallo[y_]]:=smallo[x+y];
smallo/:smallo[x_+smallo[y_]]:=smallo[x]+smallo[y];
smallo/:smallo[x_*y_]/;NumberQ[x]:=smallo[y];
smallo/:smallo[y_]*smallo[x_]:=smallo[x*y];
smallo/:Limit[smallo[x_],y__]:=smallo[Limit[x,y]];

smallo/:MakeBoxes[smallo,TraditionalForm]:="o";


(* ::Chapter:: *)
(*Manipulate expressions*)


(* ::Subchapter:: *)
(*Simplification*)


SimplifyTerms[expr_]:=Map[Simplify,expr]


(* ::Subchapter:: *)
(*Inequality*)


TriAbs[expr_,c_]:=expr/.Abs[a_-b_]->Abs[a-c]+Abs[c-b];

SplitInequality[expr_,a_,split_,f_]:=expr/.f[a,b_]->f[a,split]\[Or]f[split,a,b];
SplitGreater[expr_,a_,split_]:=SplitInequality[expr, a, split, Greater];
SplitLess[expr_,a_,split_]:=SplitInequality[expr, a, split, Less];

ToLeft[ieq_]:=Head[ieq][Subtract@@ieq,0];
ToRight[ieq_]:=Head[ieq][0, Subtract@@ Reverse @*List @@ ieq];


ReducePositive[expr_, var_, Reals]:=ReducePositive[expr,var];
ReducePositive[expr_, var_] /; ! ListQ[var] := ReducePositive[expr, {var}]
ReducePositive[expr_, vars_List] := 
  Module[{assump, toAvoid, reducedExpr}, 
   reducedExpr = Reduce[expr, vars, Reals];
   toAvoid = vars~Join~{Less, Greater, LessEqual, GreaterEqual, Equal,-1};
   assump = Cases[reducedExpr, v_ /; And @@ Map[FreeQ[v, #] &, toAvoid] :> v > 0, Infinity];
   assump = Cases[assump, v_ /; v =!= False];
   Refine[reducedExpr, assump]
];


(* ::Subchapter:: *)
(*Inactive*)


inac[a__]:=Inactive[a];

InactivateAll[expr_]:=Inactivate[expr,x_/;!MemberQ[{Plus,Power,Times},x]]
InactivateAll[expr_, heads_List]:=Inactivate[expr,x_/;!MemberQ[heads~Join~{Plus,Power,Times},x]]
InactivateAll[expr_, head_]:=Inactivate[expr,x_/;!MemberQ[{head, Plus,Power,Times},x]]

iSum=Inactive[Sum];
iInt=Inactive[Integrate];
iLog=Inactive[Log];
iLg=Inactive[Lg];
iInd = Inactive[Ind];
iFracPart=Inactive[FracPart];

headOrihead[head_]:=Alternatives[head, Inactive[head]];



(* ::Subchapter:: *)
(*factor out*)


FactorOut[expr_,fact_]:=Replace[expr, p_Plus :> fac Simplify[p/fac], All];



(* ::Subchapter:: *)
(*head*)


BringOutSum[expr_]:=BringOut[expr,iSum|Sum];
BringOutInt[expr_]:=BringOut[expr,iInt|Integrate];
BringOut[expr_,head_]:=expr//.(h:(head))[c_ f_,it:{x_Symbol,__}]/;FreeQ[c,x]:>c h[f,it];

KeepOnly[expr_,keep_]:=FixedPoint[Replace[#, a_[b_. c_, d___] /; Not[FreeQ[c, keep]] :> b a[c, d], {0, \[Infinity]}] &, expr];

ExpandHead[expr_, head_]:=expr/.HoldPattern[(h:head|Inactive[head])[a_,b___]]:>h[Expand[a],b];

SplitHead[expr_, head_, glue_:Plus]/;!ListQ[head]:=
expr//.(h:headOrihead[head])[a_~glue~b_,c___]:>h[a,c]~glue~h[b,c];
SplitHead[expr_, heads_List]:=Module[{splitfl},
splitfl=Map[(Function[expr1,SplitHead[expr1,#]])&,Reverse[heads]];
(Composition@@splitfl)[expr]]

SwitchHead[expr_,head1_,head2_]:= 
expr/.(h1:headOrihead[head1])[(h2:headOrihead[head2])[a1_,a2___],a3___] ->h2[h1[a1, a3],a2];


SplitIndex[expr_, head_, split_, glue_: Plus] := 
 expr /. (h:headOrihead[head])[a_, {x_, low_, up_,p4___}]:> 
   glue[h[a, {x, low, split, p4}], h[a, {x, split + 1, up, p4}]];

ShiftHead[expr_, head_, shift_]:=
expr/.(h:headOrihead[head])[p1_,{idx_,p2_,p3_,p4___}]:>
h[p1/.idx->idx+shift,{idx,p2-shift,p3-shift, p4}];

TruncateHead[expr_, head_, upper_]:=
expr/.(h:headOrihead[head])[p1_,{idx_,p2_,p3_,p4___}]:>
h[p1,{idx,p2,upper, p4}];

MergeHead[expr_, head_]:=
expr//.(h:headOrihead[head])[a1_,b___]+(h:headOrihead[head])[a2_,b___]->h[a1+a2,b];



(* ::Chapter:: *)
(*Misc functions*)


(* ::Subchapter:: *)
(*Lg*)


Lg[x_]:=Log[2,x];
SetAttributes[Lg,NumericFunction];
Lg/:MakeBoxes[Lg,TraditionalForm]:="lg"


(* ::Subchapter:: *)
(*FracPart*)


FracPart[x_]:=x-Floor[x];
MakeBoxes[FracPart[x_], TraditionalForm]:=TemplateBox[{MakeBoxes[x,TraditionalForm]},
    "FracPart",
    DisplayFunction->(RowBox[{"{",#, "}"}]&),
    Tooltip->"Fractional part"
]


(* ::Subchapter:: *)
(*Floor and Ceiling*)


UpperFloor[expr_]:=expr/.Floor[x_]->x;

LowerFloor[expr_]:=expr/.Floor[x_]->x-1;

Floor2Frac[expr_]:=expr/.Floor[x_]->x-Inactive[FracPart][x]


(* ::Subchapter:: *)
(*Indicator*)


ind[cond_]:=Piecewise[{{1,cond},{0,!cond}}];

iind=inac[ind];

Ind=ind;



(* ::Chapter:: *)
(*Probability*)


BringOutE[expr_] := BringOutE[expr, {}];

BringOutE[expr_, term_] /; ! ListQ[term] := 
  BringOutE[expr, {term}];

BringOutE[expr_, terms_List] := 
  Module[{expectaionHeads, termPattern, expr1},
   expectaionHeads = Conditioned | \[DoubleStruckCapitalE];
   termPattern = Alternatives @@ (Join[terms, {x_ /; NumberQ[x]}]);
   expr1 = 
    expr //. (h : expectaionHeads)[a_*(t : termPattern), b___] :> 
      t *h[a, b];
   expr1 //. (h : expectaionHeads)[a_, b___] /; NumberQ[a] :> a
   ];



(* ::Chapter:: *)
(*Summation Manipulation*)


SumOriSum=headOrihead[Sum];

ExpandSum[expr_]:=ExpandHead[expr, Sum];

ShiftSum[expr_,shift_]:=ShiftHead[expr, Sum, shift];

PrependSum[expr_,shift_]:=
expr/.(h:SumOriSum)[p1_,{idx_,p2_,p3_}]:>-h[p1,{idx,p2-shift,p2-1}]+h[p1,{idx,p2-shift,p3}];


SplitSumIndex[expr_,shift_]:=SplitIndex[expr,Sum,shift];

SwitchIntSum[expr_]:=SwitchHead[expr, Integrate, Sum];

SwitchSumInt[expr_]:=SwitchHead[expr, Sum, Integrate];

SplitSum[expr_]:=SplitHead[expr,Sum];


TruncateSum[expr_,upper_]:=TruncateHead[expr, Sum, upper];

MergeSum[expr_]:=MergeHead[expr, Sum];


(* end the private context *)
End[ ]


(* end the package context *)
EndPackage[];
