(* :Title: Zeno.m -- helper functions for manipulate symbolic equations *)

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

Ind::usage="Ind[cond]==1 if cond is True otherwise Ind[cond]=0.";
iSum::usage="iSum is a shorthand for Inactive[Sum]";
iInd::usage="iInd is a shorthand for Inactive[Ind]";
iInt::usage="iInt is a shorthand for Inactive[Integrate]";
iLog::usage="iLog is a shorthand for Inactive[Log]";
iLg::usage="iLg is a shorthand for Inactive[Lg]";

ExpandHead::usage="ExpandHead[expr, h] applies Expand to the first variable for all heads h in expr.";
SplitHead::usage="SplitHead[expr, f] split every f[a+b] in expr to f[a]+f[b].
SplitHead[expr, {f1,f2,...,fk}] split every fi[a+b] in expr to fi[a]+fi[b], for i=1...k sequentially";
SwitchHead::usage="SwitchHead[expr,h1,h2] switch the position of h1 and h2 in expr.";

TriAbs::usage="TriAbs[expr,c] turns Abs[a-b] in expr to Abs[a-c]+Abs[c-b]";

SplitInequality::usage="SplitInequality[expr,a,split,ieq] turns ieq[a, c] in expr to ieq[a,split] || ieq[split,a,c]."
SplitGreater::usage="SplitGreater[expr,a,split,ieq] turns a>c in expr to a>c || split>a>c."
SplitLess::usage="SplitLess[expr,a,split,ieq] turns a<c in expr to a<c || split<a<c."


Begin["`Private`"]    (* begin the private context (implementation*part) *)

(* ::Chapter::Closed:: *)
(*BigO function*)

MyAssumptions={k\[Element]Integers,k>=0,
m\[Element]Integers,m>=0,
n\[Element]Integers,n>=0,
l\[Element]Integers,l>=0,
Const0>0
};

$Assumptions:=ToExpression["MyAssumptions"];

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
smallo/:Limit[smallo[x_],y__]:=smallo[Limit[x,y]]

smallo/:MakeBoxes[smallo,TraditionalForm]:="o"

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

(* ::Subchapter:: *)
(*factor out*)


FactorOut[expr_,fact_]:=Replace[expr, p_Plus :> fac Simplify[p/fac], All];

(* ::Subchapter:: *)
(*head*)


ExpandHead[expr_, head_]:=expr/.HoldPattern[head[a_,b___]]:>head[Expand[a],b];

SplitHead[expr_, f_]:=expr/.f[a_,c___]:>Total@Map[(f[#,c])&,List@@Expand@a]/;!ListQ[f]
SplitHead[expr_, fl_List]:=Module[{splitfl},
splitfl=Map[(Function[expr1,SplitHead[expr1,#]])&,Reverse[fl]];
(Composition@@splitfl)[expr]]

SwitchHead[expr_,h1_,h2_]:=expr/.h1[h2[a1_,a2___],a3___]->h2[h1[a1, a3],a2]


(* ::Subchapter:: *)
(*logic expression*)


(* ::Subchapter:: *)
(*Summation Manipulation*)


sumExpand[expr_]:=expr/.(Inactive[Sum]|Sum)[p1_,p2_]:>Inactive[Sum][Expand[p1],p2]


expandSum=esumExpand;


shiftSum[sum_,shift_]:=
sum/.Inactive[Sum][p1_,{idx_,p2_,p3_}]:>
Inactive[Sum][p1/.idx->idx+shift,{idx,p2-shift,p3-shift}]


shiftSumNeg[sum_,shift_]:=sum/.Inactive[Sum][p1_,{idx_,p2_,p3_,p4_}]:>Inactive[Sum][p1/.idx->idx+shift,{idx,p2-shift,p3-shift,p4}]


prependSum[sum_,shift_]:=
sum/.Inactive[Sum][p1_,{idx_,p2_,p3_}]:>-Sum[p1,{idx,p2-shift,p2-1}]+Inactive[Sum][p1,{idx,p2-shift,p3}]


chopSum[sum_,shift_]:=
sum/.Inactive[Sum][p1_,{idx_,p2_,p3_}]:>Sum[p1,{idx,p2,p2+(shift-1)}]+Inactive[Sum][p1,{idx,p2+shift,p3}]


chopSumNeg[sum_,shift_]:=sum/.Inactive[Sum][p1_,{idx_,p2_,p3_,p4_.}]:>Sum[p1,{idx,p2,p2+(shift-1)*p4,p4}]+Inactive[Sum][p1,{idx,p2+shift*p4,p3,p4}]


factorSum[sum_,factor_]:=Module[{},sum/.(Inactive[Sum]|Sum)[p1_,p2_]:>
If[FreeQ[p1,Sum],
factor*Inactive[Sum][p1/factor//Simplify,p2],
factor*Inactive[Sum][1/factor*factorSum[p1,factor],p2]
]]


factorSumExits[sum_,factor_Symbol]:=sum/.(Inactive[Sum]|Sum)[factor*p1_,p2_]:>factor*iSum[p1,p2];
factorSumExits[sum_,factor_List]:=Fold[factorSumExits,sum,factor];


factorSumSum[sum_,factor_]:=sum/.(Inactive[Sum]|Sum)[(Inactive[Sum]|Sum)[p1_,p4_],{idx_,p2_,p3_}]:>factor*Inactive[Sum][Inactive[Sum][p1/factor//Simplify,p4],{idx,p2,p3}]


factorSumNeg[sum_,factor_]:=sum/.Inactive[Sum][p1_,{idx_,p2_,p3_,p4_.}]:>factor*Inactive[Sum][p1/factor//Simplify,{idx,p2,p3,p4}]


factorSumMinusOne[sum_]:=sum/.Inactive[Sum][p1_,{idx_,p2_,p3_}]/;p1[[1]]<0:>p1[[1]]*Inactive[Sum][p1/p1[[1]]//Simplify,{idx,p2,p3}]


switchIntSum[expr_]:=
expr/.(Inactive[Integrate]|Integrate)[p1_.*(Sum|Inactive[Sum])[p3_,p4_],p2_]:>Inactivate[Sum[Integrate[p1*p3,p2],p4],Sum|Integrate]


constSum[expr_]:=
expr/.(Inactive[Sum]|Sum)[p1_,{idx_,p2_,p3_}]/;FreeQ[p1,idx]->(p3-p2+1)*p1


splitSum[expr_]:=
expr/.(Inactive[Sum]|Sum)[p1_,p2_]/;MatchQ[p1,Plus[_,__]]:>Map[Inactive[Sum][#,p2]&,p1]


reflectShiftSum[expr_,shift_,idx1_]:=
expr/.(Inactive[Sum]|Sum)[p1_,{idx_,p2_,p3_}]:>Inactive[Sum][p1/.idx->shift-idx1,{idx1,shift-p3//Simplify,shift-p2//Simplify}]


splitIntegrate[expr_]:=
expr/.(Inactive[Integrate]|Integrate)[p1_, p2_]/;MatchQ[p1//Expand,Plus[_,__]]:>Map[Inactive[Integrate][#,p2]&,Expand[p1]]


reflectShiftSum[sum_,shift_,idx1_,idx2_]:=
sum/.(Inactive[Sum]|Sum)[p1_,{idx2,p2_,p3_}]:>Inactive[Sum][p1/.idx2->shift-idx1,{idx1,shift-p3//Simplify,shift-p2//Simplify}]


truncateSum[sum_,upper_]:=
sum/.(Inactive[Sum]|Sum)[p1_,{idx_,p2_,p3_}]:>
Inactive[Sum][p1,{idx,p2,upper}]


truncateSumLow[sum_,lower_]:=
sum/.(Inactive[Sum]|Sum)[p1_,{idx_,p2_,p3_}]:>
Inactive[Sum][p1,{idx,lower,p3}]


chopSumInactive[sum_,shift_]:=
sum/.Inactive[Sum][p1_,{idx_,p2_,p3_}]:>
Inactive[Sum][p1,{idx,p2,p2+(shift-1)}//Simplify]+Inactive[Sum][p1,{idx,p2+shift//Simplify,p3}]


canonicalSum[expr_]:=expr//. (Sum|Inactive[Sum])[p1_,p2_]*x_ :>Inactive[Sum][p1*x//Simplify,p2]


canonicalSumNeg[expr_]:=Module[{out},
(* take everything inside *)
out=canonicalSum[expr];
(* but keep -1 outside *)
out//.Inactive[Sum][-p1_,p2_]:>-Inactive[Sum][p1,p2]
]


mergeSum[expr_]:=Module[{},
expr//.Inactive[Sum][s1_,tt1_]+Inactive[Sum][s2_,tt1_]:>Inactive[Sum][s1+s2//Simplify,tt1]
]


factorSumAt[expr_,factor_,positions_]:=MapAt[factorSum[#,factor]&,expr,positions]


(* ::Subchapter:: *)
(*Brings out constant factor*)


bringsOut[expr_]:=bringsOut[expr,iSum];/!ListQ[f]
bringsOut[expr_,head_] := expr//.head[c_ f_,it:{x_Symbol,__}]/;FreeQ[c,x]:>c head[f,it];


(* ::Subchapter:: *)
(*Inequalities*)


oneSide::usage="oneSide[ieq] moves all terms of an ineqaulity to one side. 
For example oneSide[x>y] gives x-y>0";
oneSide=(Head[#][Subtract@@#,0]&)


isolate[ieq_, var_]:= ieq/.f_[a_*var,b_]->f[var, b/a]/.f_[a_,b_*var]->f[a/b, var]


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


iFracPart[a__]:=Inactive[FracPart][a]


(* ::Subchapter:: *)
(*Floor and Ceiling*)


floorRule=Floor[x_]->x


removeFloor[expr_]:=expr/.floorRule


lowerFloor[expr_]:=(expr/.floorRule)-1


floorToFrac[expr_]:=expr/.Floor[x_]->x-Inactive[FracPart][x]


(* ::Subchapter:: *)
(*Indicator*)


ind[cond_]:=Piecewise[{{1,cond},{0,!cond}}];

iind=inac[ind];

Ind=ind;


(* end the private context *)

End[ ]

(* end the package context *)
EndPackage[];
