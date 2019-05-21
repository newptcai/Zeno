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

zConst0::usage="Represent a positive constant"

zMyAssumptions::usage="zMyAssumptions replaces $Assumptions in each individual notebook. So in effect, each notebook has it own $Assumptions."

zO::usage="zO[f[x]] denote an implicit function g[x] that satisfies |g[x]|<C f[x].";
zPow2O::usage="zPow2O[expr, m, expo] turns expr to zO[b m^a] if expr=b*m^a and a<=expo";
zO2Zero::usage="zO2Zero[expr] turns all zO terms in expr to 0.";
zExpandO::usage="zExpandO[expr] turns all zO[a] terms in expr to zO[Expand[a]].";
zO2Const::usage="zO2Const[expr] turns all zO[a] terms in expr to zConst0*a.";
zo::usage="zo[f[x]] denote an implicit function g[x] that satisfies |g[x]/f[x]| -> 0 as x -> Infinity.";

zPow2o::usage="zPow2o[expr, m, expo] turns expr to zo[b m^a] if expr=b*m^a and a<=expo";
zo2Zero::usage="zo2Zero[expr] turns all zo terms in expr to 0.";
zExpando::usage="zExpando[expr] turns all zo[a] terms in expr to zo[Expand[a]].";
zo2Const::usage="zo2Const[expr] turns all zo[a] terms in expr to zConst0*a.";

zSimplifyTerms::usage="zSimplifyTerms[expr] simplify each term in expr separately";

zInactivateAll::usage="zInactivateAll[expr] applies Inactivate to all heads in expr except head in {Plus,Power,Times}.
zInactivateAll[expr,heads] applies Inactivate to all heads in expr except head in {Plus,Power,Times} or in heads.
zInactivateAll[expr,h] applies Inactivate to all heads in expr except head in {Plus,Power,Times, h}.";

zFactorOut::usage="zFactorOut[expr, fact] turns (a + fact b) in expr to fact(a/fact + b)";
zBringOut::usage="zBringOut[expr, head] take constant factors in a out of head[a, {i, c, d}] repeatedly until no such factor exists anymore."
zBringOutSum::usage="zBringOutSum[expr] take constant factors in a out of Sum[a, {i, c, d}] repeatedly until no such factor exists anymore."
zBringOutInt::usage="zBringOutInt[expr] take constant factors in a out of Integrate[a, {i, c, d}] repeatedly until no such factor exists anymore."
zBringOutTerm::usage="zBringOutTerm[expr, head, term] convert head[c term] to term head[c]."

zKeepOnly::usage="zKeepOnly[expr, keep] turns all h1[a*h2[keep], b] in expr into a*h1[h2[keep],b] until it is not possible to do so anymore."

iSum::usage="iSum is a shorthand for Inactive[Sum]";
iInd::usage="iInd is a shorthand for Inactive[Ind]";
iInt::usage="iInt is a shorthand for Inactive[Integrate]";
iLog::usage="iLog is a shorthand for Inactive[Log]";
iLg::usage="iLg is a shorthand for Inactive[Lg]";
iFracPart::usage="iFracPart is a shorthand for Inactive[FracPart].";

zExpandHead::usage="zExpandHead[expr, h] applies Expand to the first variable for all heads h in expr.";
zSplitHead::usage="zSplitHead[expr, f] split every f[a+b] in expr to f[a]+f[b].
zSplitHead[expr, {f1,f2,...,fk}] split every fi[a+b] in expr to fi[a]+fi[b], for i=1...k sequentially";
zSwitchHead::usage="zSwitchHead[expr,h1,h2] switch the position of h1 and h2 in expr.";

zSplitIndex::usage="zSplitIndex[expr, head, s, g] turns head[a, {x, l, u}] in expr \
into head[a,{x,l,s}]~g~head[a,{x,s+1,u}]";

zShiftHead::usage="zShiftHead[expr, head, shift] turns head[f[i],{i, a, b}] in expr \
into head[f[i+shift], {i, a-shift, b-shift}]"

zTruncateHead::usage="zTruncateHead[expr, head, upper] turns head[a, {i, l, u}] in expr \
into head[a, {i, l, upper}]";

zMergeHead::usage="zMergeHead[expr, head] turns head[a1, b]+head[a2,b] in expr \
into head[a1+a2,b]."

zBringIn::usage="zBringIn[expr,head] turns a head[b, c] in expr to head[a*b,c]."

zTriAbs::usage="zTriAbs[expr,c] turns Abs[a-b] in expr to Abs[a-c]+Abs[c-b]";

zToLeft::usage="zToLeft[ieq] moves all terms of the inequality ieq to one left-hand-side."
zToRight::usage="zToRight[ieq] moves all terms of the inequality ieq to one right-hand-side."

zSplitInequality::usage="zSplitInequality[expr,a,split,ieq] turns ieq[a, c] in expr to ieq[a,split] || ieq[split,a,c]."
zSplitGreater::usage="zSplitGreater[expr,a,split,ieq] turns a>c in expr to a>c || split>a>c."
zSplitLess::usage="zSplitLess[expr,a,split,ieq] turns a<c in expr to a<c || split<a<c."

zReducePositive::usage="zReducePositive[expr, vars] reduces the statement expr by \
solving equations or inequalities for vars and eliminating quantifiers, \
assuming that all parameters in expr except vars are positive real numbers."

Lg::usage="Lg[x] is a shorthand for Log[2,x]";
Ind::usage="Ind[cond]==1 if cond is True. Otherwise Ind[cond]==0.";

FracPart::usage="FracPart[x] is the fractional part of x, i.e., FracPart[x]==x-Floor[x]. Note this different from the system function FractionalPart if x<0.";
zFloor2Frac::usage="zFloor2Frac[expr] turns Floor[x] in expr to x-FracPart[x]."
zUpperFloor::usage="zUpperFloor[expr] turns Floor[x] in expr to x."
zLowerFloor::usage="zLowerFloor[expr] turns Floor[x] in expr to x-1."

zBringOutE::usage="zBringOutE[expr, terms] take all members of terms and constants out of \
\[DoubleStruckCapitalE][a]";

\[DoubleStruckCapitalE]::usage="\[DoubleStruckCapitalE][x] stands for the expectation of x. \
It does not do any computation.";

\[DoubleStruckCapitalP]::usage="\[DoubleStruckCapitalP][x] stands for the probability of x. \
It does not do any computation.";

zExpandSum::usage="zExpandSum[expr] applies Expand to all summands of Sum in expr."

zShiftSum::usage="zShiftSum[expr, shift] turns Sum[f[i],{i, a, b}] in expr \
into Sum[f[i+shift], {i, a-shift, b-shift}]."

zPrependSum::usage="zPrependSum[expr, shift] turns Sum[f[i],{i, a, b}] in expr \
into Sum[f[i], {i, a-shift, b-shift}]-Sum[f[i], {i, a-shift, a-1}]."

zSplitSumIndex::usage="zSplitSumIndex[expr, s] turns Sum[a, {x, l, u}] in expr \
into Sum[a,{x,l,s}]+Sum[a,{x,s+1,u}].";

zSwitchIntSum::usage="zSwitchIntSum[expr] turns Integrate[Sum[a[x,i],{i, l0, u0}], {x,l1,u1}] \
in expri into Sum[Integrate[a[x,i],{x,l1,u1}], {i, l0, u0}]."

zSwitchSumInt::usage="zSwitchSumInt[expr] turns Sum[Integrate[a[x,i],{x,l1,u1}], {i, l0, u0}] \
in expri into Integrate[Sum[a[x,i],{i, l0, u0}], {x,l1,u1}]."

zSplitSum::usage="zSplitSum[expr] turns Sum[a+b,c] in expr into Sum[a,c]+Sum[b,c]."

zTruncateSum::usage="zTruncateSum[expr, upper] turns Sum[a, {i, l, u}] in expr \
into Sum[a, {i, l, upper}]";

zMergeSum::usage="zMergeSum[expr, head] turns Sum[a1, b]+Sum[a2,b] in expr \
into Sum[a1+a2,b]."

Begin["`Private`"]    (* begin the private context (implementation*part) *)


(* ::Chapter:: *)
(*Assumptions*)


zMyAssumptions={ zConst0>0 };

$Assumptions:=ToExpression["zMyAssumptions"];


(* ::Chapter:: *)
(*Asymptotics*)


(* ::Subchapter:: *)
(*zO notation*)


zPow2O[expr_,m_,expo_]:=With[{mexpo=Exponent[expr,m]}, If[Simplify[mexpo<=expo],zO[m^mexpo]*expr/m^mexpo,expr,expr]];
zO2Zero[expr_]:=expr/.zO[_]:>0;
zExpandO[expr_]:=zExpandHead[expr,zO];
zO2Const[expr_]:=expr/.zO[a_]->zConst0 a;

zO[0]=0;
zO[x_]/;NumberQ[x]:=zO[1];
zO/:zO[x_]+zO[y_]:=zO[x+y];
zO/:zO[x_]-zO[y_]:=zO[x+y];
zO/:y_*zO[x_]:=zO[x*y];
zO/:zO[x_+zO[y_]]:=zO[x+y];
zO/:zO[x_+zo[y_]]:=zO[x]+zo[y];
zO/:zO[x_*y_]/;NumberQ[x]:=zO[y];
zO/:zO[y_]*zO[x_]:=zO[x*y];
zO/:zO[y_]^p_:=zO[y^p];
zO/:Limit[zO[x_],y__]:=zO[Limit[x,y]]

zO/:MakeBoxes[zO,TraditionalForm]:="O"


(* ::Subchapter:: *)
(*zo notation*)


zPow2o[expr_,m_,expo_]:=With[{mexpo=Exponent[expr,m]}, If[Simplify[mexpo<=expo],zo[m^mexpo]*expr/m^mexpo,expr,expr]];
zo2Zero[expr_]:=expr/.zo[_]:>0;
zExpando[expr_]:=zExpandHead[expr,zo];
zo2Const[expr_]:=expr/.zo[a_]->zConst0 a;

zo[0]=0;
zo[x_]/;NumberQ[x]:=zo[1];
zo/:zo[x_]+zo[y_]:=zo[x+y];
zo/:zo[x_]-zo[y_]:=zo[x+y];
zo/:y_*zo[x_]:=zo[x*y];
zo/:zo[x_+zo[y_]]:=zo[x+y];
zo/:zo[x_+zo[y_]]:=zo[x]+zo[y];
zo/:zo[x_*y_]/;NumberQ[x]:=zo[y];
zo/:zo[y_]*zo[x_]:=zo[x*y];
zo/:Limit[zo[x_],y__]:=zo[Limit[x,y]];

zo/:MakeBoxes[zo,TraditionalForm]:="o";


(* ::Chapter:: *)
(*Manipulate expressions*)


(* ::Subchapter:: *)
(*Simplification*)


zSimplifyTerms[expr_]:=Map[Simplify,expr]


(* ::Subchapter:: *)
(*Inequality*)


zTriAbs[expr_,c_]:=expr/.Abs[a_-b_]->Abs[a-c]+Abs[c-b];

zSplitInequality[expr_,a_,split_,f_]:=expr/.f[a,b_]->f[a,split]\[Or]f[split,a,b];
zSplitGreater[expr_,a_,split_]:=zSplitInequality[expr, a, split, Greater];
zSplitLess[expr_,a_,split_]:=zSplitInequality[expr, a, split, Less];

zToLeft[ieq_]:=Head[ieq][Subtract@@ieq,0];
zToRight[ieq_]:=Head[ieq][0, Subtract@@ Reverse @*List @@ ieq];


zReducePositive[expr_, var_, Reals]:=zReducePositive[expr,var];
zReducePositive[expr_, var_] /; ! ListQ[var] := zReducePositive[expr, {var}]
zReducePositive[expr_, vars_List] := 
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

zInactivateAll[expr_]:=Inactivate[expr,x_/;!MemberQ[{Plus,Power,Times},x]]
zInactivateAll[expr_, heads_List]:=Inactivate[expr,x_/;!MemberQ[heads~Join~{Plus,Power,Times},x]]
zInactivateAll[expr_, head_]:=Inactivate[expr,x_/;!MemberQ[{head, Plus,Power,Times},x]]

iSum=Inactive[Sum];
iInt=Inactive[Integrate];
iLog=Inactive[Log];
iLg=Inactive[Lg];
iInd = Inactive[Ind];
iFracPart=Inactive[FracPart];

headOrihead[head_]:=Alternatives[head, Inactive[head]];



(* ::Subchapter:: *)
(*factor out*)


zFactorOut[expr_,fact_]:=Replace[expr, p_Plus :> fac Simplify[p/fac], All];



(* ::Subchapter:: *)
(*head*)


zBringOutSum[expr_]:=zBringOut[expr,iSum|Sum];
zBringOutInt[expr_]:=zBringOut[expr,iInt|Integrate];
zBringOut[expr_,head_]:=expr//.(h:(head))[c_ f_,it:{x_Symbol,__}]/;FreeQ[c,x]:>c h[f,it];
zBringOutTerm[expr_,head_,term_]:=expr/.head[p0_, p1__]:>term head[p0/term, p1];

zKeepOnly[expr_,keep_]:=FixedPoint[Replace[#, a_[b_. c_, d___] /; Not[FreeQ[c, keep]] :> b a[c, d], {0, \[Infinity]}] &, expr];

zExpandHead[expr_, head_]:=expr/.HoldPattern[(h:head|Inactive[head])[a_,b___]]:>h[Expand[a],b];

zSplitHead[expr_, head_, glue_:Plus]/;!ListQ[head]:=
expr//.(h:headOrihead[head])[a_~glue~b_,c___]:>h[a,c]~glue~h[b,c];
zSplitHead[expr_, heads_List]:=Module[{splitfl},
splitfl=Map[(Function[expr1,zSplitHead[expr1,#]])&,Reverse[heads]];
(Composition@@splitfl)[expr]]

zSwitchHead[expr_,head1_,head2_]:= 
expr/.(h1:headOrihead[head1])[(h2:headOrihead[head2])[a1_,a2___],a3___] ->h2[h1[a1, a3],a2];

zSplitIndex[expr_, head_, split_, glue_: Plus] := 
 expr /. (h:headOrihead[head])[a_, {x_, low_, up_,p4___}]:> 
   glue[h[a, {x, low, split, p4}], h[a, {x, split + 1, up, p4}]];

zShiftHead[expr_, head_, shift_]:=
expr/.(h:headOrihead[head])[p1_,{idx_,p2_,p3_,p4___}]:>
h[p1/.idx->idx+shift,{idx,p2-shift,p3-shift, p4}];

zTruncateHead[expr_, head_, upper_]:=
expr/.(h:headOrihead[head])[p1_,{idx_,p2_,p3_,p4___}]:>
h[p1,{idx,p2,upper, p4}];

zMergeHead[expr_, head_]:=
expr//.(h:headOrihead[head])[a1_,b___]+(h:headOrihead[head])[a2_,b___]->h[a1+a2,b];

zBringIn[expr_,head_]:=expr//. a_*head[b_,c___]:>head[a b,c]


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


zUpperFloor[expr_]:=expr/.Floor[x_]->x;

zLowerFloor[expr_]:=expr/.Floor[x_]->x-1;

zFloor2Frac[expr_]:=expr/.Floor[x_]->x-Inactive[FracPart][x]


(* ::Subchapter:: *)
(*Indicator*)


ind[cond_]:=Piecewise[{{1,cond},{0,!cond}}];

iind=inac[ind];

Ind=ind;



(* ::Chapter:: *)
(*Probability*)


zBringOutE[expr_] := zBringOutE[expr, {}];

zBringOutE[expr_, term_] /; ! ListQ[term] := 
  zBringOutE[expr, {term}];

zBringOutE[expr_, terms_List] := 
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

zExpandSum[expr_]:=zExpandHead[expr, Sum];

zShiftSum[expr_,shift_]:=zShiftHead[expr, Sum, shift];

zPrependSum[expr_,shift_]:=
expr/.(h:SumOriSum)[p1_,{idx_,p2_,p3_}]:>-h[p1,{idx,p2-shift,p2-1}]+h[p1,{idx,p2-shift,p3}];


zSplitSumIndex[expr_,shift_]:=zSplitIndex[expr,Sum,shift];

zSwitchIntSum[expr_]:=zSwitchHead[expr, Integrate, Sum];

zSwitchSumInt[expr_]:=zSwitchHead[expr, Sum, Integrate];

zSplitSum[expr_]:=zSplitHead[expr,Sum];


zTruncateSum[expr_,upper_]:=zTruncateHead[expr, Sum, upper];

zMergeSum[expr_]:=zMergeHead[expr, Sum];


(* end the private context *)
End[ ]


(* end the package context *)
EndPackage[];
