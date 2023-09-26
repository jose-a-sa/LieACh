(* ::Package:: *)

(* Wolfram Language Package *)

Unprotect["LieARTCharacters`*"];
ClearAll["LieARTCharacters`*"];


BeginPackage["LieARTCharacters`", {"LieART`"}]


DominantWeightOrder::usage = "\
DominantWeightOrder[\!\(\*SubscriptBox[
StyleBox[\"w\", \"TI\"], 
StyleBox[\"1\", \"TR\"]]\),\!\(\*SubscriptBox[
StyleBox[\"w\", \"TI\"], 
StyleBox[\"2\", \"TR\"]]\)] computes the weak ordering between weights \!\(\*SubscriptBox[
StyleBox[\"w\", \"TI\"], 
StyleBox[\"1\", \"TR\"]]\) and \!\(\*SubscriptBox[
StyleBox[\"w\", \"TI\"], 
StyleBox[\"2\", \"TR\"]]\).";
HighestWeights::usage = "\
HighestWeights[\!\(\*
StyleBox[\"list\", \"TI\"]\)] returns the list of highest weights from the \!\(\*
StyleBox[\"list\", \"TI\"]\) of weights of the same algebra.";
HighestWeightsFrom::usage = "\
HighestWeightsFrom[\!\(\*
StyleBox[\"expr\", \"TI\"]\), \!\(\*
StyleBox[\"vars\", \"TI\"]\), \!\(\*
StyleBox[\"algebra\", \"TI\"]\)] returns a list of highest weights found in the expr taken as a character of algebra";
Ch::usage = "Ch[irrep] returns a pure function representing the character of irrep.";
CharacterDecomposition::usage = "\
CharacterDecomposition[\!\(\*
StyleBox[\"expr\", \"TI\"]\), \!\(\*
StyleBox[\"vars\", \"TI\"]\), \!\(\*
StyleBox[\"algebra\", \"TI\"]\)] decomposes \!\(\*
StyleBox[\"expr\", \"TI\"]\) into characters of irreps, returning a key-value Association with the corresponding coefficients.
CharacterDecomposition[\!\(\*
StyleBox[\"algebra\", \"TI\"]\)][\!\(\*
StyleBox[\"expr\", \"TI\"]\), \!\(\*
StyleBox[\"vars\", \"TI\"]\)] is equivalent (alias) to CharacterDecomposition[\!\(\*
StyleBox[\"expr\", \"TI\"]\), \!\(\*
StyleBox[\"vars\", \"TI\"]\), \!\(\*
StyleBox[\"algebra\", \"TI\"]\)].
CharacterDecomposition[\!\(\*
StyleBox[\"expr\", \"TI\"]\), \!\(\*
StyleBox[\"vars\", \"TI\"]\)] computes the character decomposition of \!\(\*
StyleBox[\"expr\", \"TI\"]\) for the algebra \!\(\*
StyleBox[SubscriptBox[\"A\", \"n\"], \"TI\"]\), where \!\(\*
StyleBox[\"n\", \"TI\"]\) is the number of \!\(\*
StyleBox[\"vars\", \"TI\"]\).";
MonomialCoefficient::usage = "MonomialCoefficient[expr, vars, powers] returns";
WeylGroupOrder::usage = "WeylGroupOrder[algebra] returns the number of algebra elements.";
FugacityMap::usage = "FugacityMap[origin, destination]";

StepMonitorFunction::usage = "StepMonitorFunction is an option for CharacterDecomposition to help monitor each step in the iteration.";

$SaveCharacterDefinitions::usage = "Important performance saving tool";

$SaveCharacterDefinitions = True;


Begin["`Private`"];


DynkinLabelQ[n__Integer?NonNegative] = True;
DynkinLabelQ[_] = False;

AlgebraQ[ Algebra[A | B | C | D][_Integer] ] = True;
AlgebraQ[E6 | E7 | E8 | G2 | F4] = True;
AlgebraQ[_] = False;

AlgebraClassQ[A | B | C | D] = True;
AlgebraClassQ[E6 | E7 | E8 | G2 | F4] = True;
AlgebraClassQ[_] = False;

ProductAlgebraQ[ ProductAlgebra[__?AlgebraQ] ] = True;
ProductAlgebraQ[_] = False;

IrrepQ[ Irrep[A | B | C | D][__?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[E6][(Repeated[_, {6}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[E7][(Repeated[_, {7}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[E8][(Repeated[_, {8}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[F4][(Repeated[_, {4}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[G2][(Repeated[_, {2}])?DynkinLabelQ] ] = True;
IrrepQ[_] = False;

ProductIrrepQ[ ProductIrrep[__?IrrepQ] ] = True;
ProductIrrepQ[_] = False;

SingleOrProdIrrepQ[_?IrrepQ] = True;
SingleOrProdIrrepQ[_?ProductIrrepQ] = True;
SingleOrProdIrrepQ[_] = False;

IrrepTimesQ[ HoldPattern[IrrepTimes][_, _?SingleOrProdIrrepQ] ] = True;
IrrepTimesQ[_] = False;

IrrepPlusQ[ IrrepPlus[s: (_?IrrepTimesQ | _?SingleOrProdIrrepQ) ..] ] :=
  SameQ @@ Algebra@IrrepPlus[s];
IrrepPlusQ[_] = False;

WeightQ[ (WeightAlpha | Weight)[A | B | C | D][__] ] = True;
WeightQ[ (WeightAlpha | Weight)[E6][(Repeated[_, {6}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[E7][(Repeated[_, {7}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[E8][(Repeated[_, {8}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[F4][(Repeated[_, {4}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[G2][(Repeated[_, {2}])] ] = True;
WeightQ[_] = False;

ProductWeightQ[ ProductWeight[__?WeightQ] ] = True;
ProductWeightQ[_] = False;

SingleOrProdWeightQ[_?WeightQ] = True;
SingleOrProdWeightQ[_?ProductWeightQ] = True;
SingleOrProdWeightQ[_] = False;

ToDynkinLabel[ ProductIrrep[ir__?IrrepQ] ] := Map[ToDynkinLabel, {ir}];
ToDynkinLabel[ Irrep[_][ns__?DynkinLabelQ] ] := {ns};


WeylGroupOrder[ Algebra[A][n_Integer?NonNegative] ] := (n+1)!;
WeylGroupOrder[ Algebra[B][n_Integer?NonNegative] ] := (2^n) n!;
WeylGroupOrder[ Algebra[C][n_Integer?NonNegative] ] := (2^n) n!;
WeylGroupOrder[ Algebra[D][n_Integer?Positive] ] := (2^(n-1)) n!;
WeylGroupOrder[ E6 ] = 51840;
WeylGroupOrder[ E7 ] = 2903040;
WeylGroupOrder[ E8 ] = 696729600;
WeylGroupOrder[ F4 ] = 1152;
WeylGroupOrder[ G2 ] = 12;
SetAttributes[WeylGroupOrder, {ReadProtected, Protected}];


Ch[{lbl__?DynkinLabelQ}] := 
  Ch[A, {lbl}];
Ch[g_?AlgebraQ, {lbl__?DynkinLabelQ}] /; (!SameQ[Length@{lbl}, Rank@g]) :=
  Null /; Message[Ch::errmatchrk, g, {lbl}];
Ch[g: (_?AlgebraQ | _?AlgebraClassQ), {lbl__?DynkinLabelQ}] := 
  Ch[ Irrep[AlgebraClass@g][lbl] ];
Ch[w: (WeightAlpha[g_][lbl__]) ] :=
  Ch[ OmegaBasis@w ];
Ch[ Weight[g_][lbl__] ] /; (!IrrepQ[ Irrep[g][lbl] ]) :=
  Null /; Message[Ch::errirrep, Irrep[g][lbl] ];
Ch[ Weight[g_][lbl__] ] :=
  Ch[ Irrep[g][lbl] ];
Ch[ ProductWeight[w__] ] /; (!ProductIrrepQ[ProductIrrep @@ ToIrrep@OmegaBasis@{w}]) :=
  Null /; Message[Ch::errirrep, ProductIrrep @@ ToIrrep@OmegaBasis@{w}] ;
Ch[ ProductWeight[w__] ] :=
  Ch[ ProductIrrep @@ ToIrrep@OmegaBasis@{w} ];
Ch[rep_?IrrepQ] :=
  Module[{ws, f, func},
    ws = MapAt[Apply[List], WeightSystemWithMul[rep], {All, 1}];
    f = Total[(#2* Apply[Times, Array[Slot, Rank@rep]^#1] &) @@@ ws];
    func = Function[Evaluate@f];
    If[$SaveCharacterDefinitions,
      Unprotect[ Ch ];
      Ch[ rep ] = Evaluate[func];
      Protect[ Ch ];
    ];
    Return[func];
  ];
Ch[{gs: Repeated[_?AlgebraQ, {2, Infinity}]}, lbl: {{__?DynkinLabelQ} ..}] :=
  Ch[ProductAlgebra[gs], lbl]
Ch[g_?ProductAlgebraQ, lbl: {{__?DynkinLabelQ} ..}] /; (!SameQ[Length@g, Length@lbl]) :=
  Null /; Message[Ch::errmatchcomp, g, lbl];
Ch[g_?ProductAlgebraQ, lbl: {{__?DynkinLabelQ} ..}] /; (!SameQ[Rank/@List@@g, Length/@lbl]) :=
  Null /; Message[Ch::errmatchrk, g, lbl];
Ch[g_?ProductAlgebraQ, lbl: {{__?DynkinLabelQ} ..}] :=
  Ch[ MapThread[Irrep[AlgebraClass@#1]@@#2 &, {List@@g, lbl}] ];
Ch[{reps__?IrrepQ}] :=
  Ch[ ProductIrrep[reps] ];
Ch[prodRep_?ProductIrrepQ] :=
  Module[{reps, rnks, f, func},
    reps = List @@ prodRep;
    rnks = Rank /@ reps;
    f = Times @@ MapThread[
      Ch[#1] @@ Array[Slot, #2, #3] &,
      {reps, rnks, Accumulate[{1, Splice@Most@rnks}]}
    ];
    func = Function[Evaluate@f];
    Return[func];
  ];
Ch[repSum_IrrepPlus?IrrepPlusQ] :=
  Module[{f, func, rnk},
    rnk = Rank[repSum];
    f = Sum[Ch[r] @@ Array[Slot, rnk], {r, List@@repSum}];
    func = Function[Evaluate@f];
    Return[func];
  ];
Ch[repSum_IrrepPlus] := 
  Null /; Message[Ch::errirrepsum];
Ch[repTimes_IrrepTimes?IrrepTimesQ] :=
  Module[{rnk, c, rep, f, func},
    rnk = Rank[repTimes];
    {c, rep} = List @@ repTimes;
    f = c * (Ch[rep] @@ Array[Slot, rnk]);
    func = Function[Evaluate@f];
    Return[func];
  ];
Ch::errmatchrk = "The rank of the algebra `1` does not match dimension of representation `2`."
Ch::errmatchrksum = "The rank of the irrep sum does not match for all summands."
Ch::errirrep = "`1` is not a valid irrep."
Ch::errirrepsum = "The sum is not a valid representation. Check each factor is a irrep of the same algebra."
SetAttributes[Ch, {ReadProtected, Protected}];


DominantWeightOrder[w1_?DominantQ, w2_?DominantQ] /; SameQ[Algebra@w1, Algebra@w2] :=
  Module[{patt},
    patt[argPatt_] := Alternatives[
      WeightAlpha[_][argPatt],
      ProductWeight[(WeightAlpha[_][argPatt]) ..]
    ];
    (* needed to update ProductWeight to use linear space properties *)
    Switch[AlphaBasis[w1 - w2],
      patt[0 ..], 0,
      patt[__Integer?NonNegative], -1,
      patt[__Integer?NonPositive], 1,
      _, Undefined
    ]
  ];
DominantWeightOrder[w1_?DominantQ, w2_?DominantQ] := Message[DominantWeightOrder::algerr];
DominantWeightOrder[w1_, w2_] := Message[DominantWeightOrder::argerr];
DominantWeightOrder::algerr = "Algebras of the dominant weights do not match.";
DominantWeightOrder::argerr = "Arguments are not dominant weights."
SetAttributes[DominantWeightOrder, {ReadProtected, Protected}];


HighestWeights[ls : {__?WeightQ} | {__?ProductWeightQ}] /; Not[SameQ @@ Map[Algebra, ls]] := 
  Null /; Message[HighestWeights::wtgmtch];
HighestWeights[ls : {__?WeightQ} | {__?ProductWeightQ}] :=
  Module[{g, rk, domW, ss, nDomW},
    g = AlgebraClass@First[ls];
    rk = Length@First[ls];
    domW = DeleteDuplicates@DominantWeights[ls];
    nDomW = Length[domW];
    If[nDomW == 0,
      Return[{}]
    ];
    (*faster than using RelationGraph and picking top vertices*)
    ss = AssociationThread[
      Subsets[Range@nDomW, {2}],
      DominantWeightOrder @@@ Subsets[domW, {2}]
    ];
    Delete[domW, Union@KeyValueMap[Drop[#1,-#2] &]@DeleteCases[Undefined]@ss ]
  ];
HighestWeights::wtgmtch = "Weights are not of the same algebra.";
SetAttributes[HighestWeights, {ReadProtected, Protected}];


HighestWeightsFrom[{gs__?AlgebraQ}][expr_, {vars__}] :=
  HighestWeightsFrom[expr, {vars}, ProductAlgebra[gs] ];
HighestWeightsFrom[g: (_?AlgebraQ | _?AlgebraClassQ | _?ProductAlgebraQ)][expr_, {vars__}] :=
  HighestWeightsFrom[expr, {vars}, g];
HighestWeightsFrom[expr_, {vars__}, g: (_?AlgebraQ | _?ProductAlgebraQ)] /; (!SameQ[Length[{vars}], Rank@g]) :=
  Message[HighestWeightsFrom::lenerr, g, {vars}];
HighestWeightsFrom[expr_, {vars__}, g : (_?AlgebraQ | _?AlgebraClassQ) : A] :=
  Module[{rk, gclass, v0, W},
    rk = Length[{vars}];
    gclass = Switch[g, 
      A | B | C | D, Algebra[g][rk],
      _, g];
    v0 = Variables[{vars}];
    (* possible with GroebnerBasis`DistributedTermsList *)
    W = DeleteDuplicates@Cases[
      (Exponent[#, {vars}] &) /@ MonomialList[ expr, Sort@Join[v0, 1/v0] ],
      {ns__Integer} :> Weight[AlgebraClass@g][ns]
    ];
    If[Length[W] == 0,
      Return[{}]
    ];
    HighestWeights[W]
  ];
HighestWeightsFrom[expr_, {vars__}, g_?ProductAlgebraQ] :=
  Module[{gs, rk, v0, varsByRk, flattenA, foldF, coef},
    gs = List @@ g;
    rk = Rank /@ gs;
    v0 = Variables[{vars}];
    varsByRk = MapThread[{vars}[[#1;;#2]] &, 
      ({Join[{0}, Most@#]+1, #} &)@Accumulate@rk
    ];
    flattenA = Association@*KeyValueMap[
      Function[{t, r}, 
        KeyValueMap[Splice@Prepend[{#1}, t] -> #2 &, Association@r] 
      ]
    ];
    foldF[{gg_, vv_}] := KeyMap[First]@*flattenA@*Map[
      Function[x, AssociationMap[
        MonomialCoefficient[x, vv, List @@ #] &, 
        HighestWeightsFrom[gg][x, vv] ]
      ] ]@*KeyMap[Splice];
    coef = Fold[
      foldF[#2][#1] &,
      Association[{} -> Expand@expr],
      Transpose[{gs, varsByRk}]
    ];
    (* possible with GroebnerBasis`DistributedTermsList *)
    Keys@KeyMap[Apply@ProductWeight, coef]
  ];
HighestWeightsFrom::lenerr = "Rank of `1` and length of `2` do not match."
SetAttributes[HighestWeightsFrom, {ReadProtected, Protected}];


MonomialCoefficient[e_, {v__}, {n__?NumericQ}] /; (!SameQ[ Length[{v}], Length[{n}] ]) := 
  Null /; Message[MonomialCoefficient::lenerr, {v}, {n}] ;
MonomialCoefficient[e_, {v__}, {n__?NumericQ}] := 
  Fold[
    Function[{x, pair}, Coefficient[x, First@pair, Last@pair] ],
    e, 
    Transpose[{{v}, {n}}]
  ];
MonomialCoefficient::lenerr = "Length of `1` and `2` do not match.";
SetAttributes[MonomialCoefficient, {ReadProtected, Protected}];


Options[CharacterDecomposition] = {MaxIterations -> Automatic, StepMonitorFunction -> None};

CharacterDecomposition[{gs__?AlgebraQ}][expr_, {vars__}, opts : OptionsPattern[CharacterDecomposition] ] :=
  CharacterDecomposition[expr, {vars}, ProductAlgebra[gs], opts];
CharacterDecomposition[g : (_?AlgebraQ | _?AlgebraClassQ | _?ProductAlgebraQ)][expr_, {vars__}, 
    opts : OptionsPattern[CharacterDecomposition] ] := 
  CharacterDecomposition[expr, {vars}, g, opts];
CharacterDecomposition[expr_, {vars__}, g: (_?AlgebraQ | _?ProductAlgebraQ), 
    opts : OptionsPattern[CharacterDecomposition] ] /; (!SameQ[Length[{vars}], Rank@g]) :=
	Message[CharacterDecomposition::lenerr, g, {vars}];
CharacterDecomposition[expr_, {vars__}, g :(_?AlgebraQ | _?AlgebraClassQ | _?ProductAlgebraQ) : A, 
    opts : OptionsPattern[CharacterDecomposition] ] :=
  Module[{toIR, maxIter, stepF, chars, hws, nestF, testF, res},
    toIR = ReplaceAll[ProductWeight -> ProductIrrep]@*ToIrrep;
    maxIter = OptionValue[CharacterDecomposition, {opts}, MaxIterations] //
      Switch[#, 
        _Integer?Positive | Infinity, #, 
        Automatic, 5000,
        _, Message[CharacterDecomposition::optarg, MaxIterations, "positive Integer", Automatic]; 5000
      ] &;
    stepF = OptionValue[CharacterDecomposition, {opts}, StepMonitorFunction] //
      Switch[#, 
        None | Automatic, (Null &), 
        _, #
      ] &;
    {chars, hws} = {Association[], List[]};
    nestF[e_] := Block[{ws, coefs},
      ws = toIR@HighestWeightsFrom[g][e, {vars}];
      coefs = Map[
        (MonomialCoefficient[e, {vars}, Flatten@#] &),
        ReplaceAll[{ProductIrrep -> List, Irrep[_] -> List}]@ws
      ];
      stepF[e, ws, Reverse@chars];
      AppendTo[hws, ws];
      PrependTo[chars, Thread[ws -> coefs] ];
      Expand[e - Map[(Ch[#][vars] &), ws] . coefs]
    ];
    testF[e_] := {MatchQ[hws, {__, {} ..}], PossibleZeroQ[e]};
    res = NestWhile[nestF, expr, Not@*Apply[Or]@*testF, 1, maxIter];
    Switch[testF@res,
      {False, False}, 
      Message[CharacterDecomposition::incmpl, toIR@HighestWeightsFrom[g][res, {vars}] ],
      {True, False}, 
      Message[CharacterDecomposition::domwerr, res]; Return[$Failed]
    ];
    Reverse@Select[chars, Not@*PossibleZeroQ]
  ];
CharacterDecomposition::optarg = "Option `1` must be a `2`. Setting value to `3`."
CharacterDecomposition::lenerr = "Rank of `1` and length of `2` do not match.";
CharacterDecomposition::incmpl = "Decomposition might be incomplete, as highest weights `1` as still present. \
Pleases try to increase MaxIterations option.";
CharacterDecomposition::domwerr = "No dominant weights found in non-zero remainder expression `1`.";
SetAttributes[CharacterDecomposition, {ReadProtected, Protected}];


FugacityMap[g_?AlgebraQ, gsub : (_?AlgebraQ | ProductAlgebra[(_?AlgebraQ | U1) ..])] :=
  Enclose[Module[{P, map},
    P = ProjectionMatrix[g, gsub];
    ConfirmAssert[MatchQ[P, _?MatrixQ], Message[FugacityMap::nosubalg, g, gsub] ];
    map = Times @@@ (Array[Subscript[\[FormalZ], #] &, Length@#]^# &) /@ Transpose[P];
    Thread[Array[Subscript[\[FormalZ], #] &, Length@map] -> map]
  ], Null &];
FugacityMap::nosubalg = "`1` does not have `2` as a subalgebra. Try changing the order in `2`.";
SetAttributes[FugacityMap, {ReadProtected, Protected}];


End[]

EndPackage[]

