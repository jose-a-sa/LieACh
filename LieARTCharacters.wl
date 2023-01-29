(* ::Package:: *)

getLieART[]:=
  Module[{paclet, res, setStdForm},
    setStdForm[] := If[$Notebooks,
      SetOptions[EvaluationNotebook[], 
        CommonDefaultFormatTypes -> {"Output" -> StandardForm}
      ];
    ];
    If[AnyTrue[$Packages, StringMatchQ["LieART`"] ],
      setStdForm[]; Return[Null]
    ];
    paclet = PacletFind["LieART"];
    If[MatchQ[paclet, {}], 
      Check[installLieART["2.1.0"], Return@$Failed]
    ];
    res = Quiet@Needs["LieART`"];
    setStdForm[];
    res
  ];

installLieART[version_String : "2.1.0"] := 
  Module[{json, download, tempDir, target, pacletObj, paclet, res},
    Check[
      download="https://lieart.hepforge.org/downloads/LieART-"<>version<>".zip";
      tempDir = CreateDirectory[];
      target= FileNameJoin[{tempDir, "LieART-"<>version<>".zip"}];
      If[$Notebooks, 
        PrintTemporary@Labeled[ProgressIndicator[Appearance->"Necklace"], "Downloading LieART...", Right],
        Print["Downloading LieART..."]
      ];
      URLSave[download,target],
      Return[$Failed]
    ];
    If[FileExistsQ[target],
      ExtractArchive[target, tempDir, OverwriteTarget->True];
      res = If[$VersionNumber >= 12.1,
        pacletObj = PacletObject[<|
          "Name" -> "LieART", "Version" -> version, 
          "MathematicaVersion" -> "6+",
          "Extensions" -> {
            {"Kernel", "Context" -> "LieART`"},
            {"Documentation", Language -> All, MainPage -> "Guides/LieART"}
        }|>];
        Put[pacletObj, FileNameJoin[{tempDir, "LieART", "PacletInfo.m"}] ];
        paclet = CreatePacletArchive@FileNameJoin[{tempDir, "LieART"}];
        PacletInstall[paclet, ForceVersionInstall->True],
        pacletObj = Paclet[
          Name -> "LieART", Version -> version,
          MathematicaVersion -> "6+",
          Extensions -> {
            {"Kernel", "Root" -> ".", "Context" -> "LieART`"},
            {"Documentation", Language -> All, MainPage -> "Guides/LieART"}
          }
        ];
        Put[pacletObj, FileNameJoin[{tempDir, "LieART", "PacletInfo.m"}] ];
        paclet = PackPaclet@FileNameJoin[{tempDir, "LieART"}];
        PacletInstall[paclet, IgnoreVersion->True]
      ];
      DeleteDirectory[tempDir, DeleteContents->True];
      Return[res],
      Return[$Failed]
    ];
  ];


getLieART[];


Remove[getLieART];
Remove[installLieART];


(* LieART FIXING *)

Rank[LieART`Private`productAlgebra_ProductAlgebra] := 
  Total[Rank /@ (List @@ LieART`Private`productAlgebra)];
Rank[LieART`Private`productIrrep_ProductIrrep] := 
  Total[Rank /@ (List @@ LieART`Private`productIrrep)];
Rank[LieART`Private`productWeight_ProductWeight] := 
  Total[Rank /@ (List @@ LieART`Private`productWeight)];
Rank[LieART`Private`irrepSum_IrrepPlus] :=
  Module[{gs},
    gs = Union@Algebra[LieART`Private`irrepSum];
    If[Length@gs > 1, Message[Rank::irrplusdiff, gs] ];
    Max[Rank /@ gs]
  ];
Rank::irrplusdiff = "IrrepPlus contains irreps of different algebras `1`. Returning the maximal rank instead.";
Rank[LieART`Private`irrepTimes_IrrepTimes] :=
  Max[Rank /@ Cases[List @@ LieART`Private`irrepTimes, _?(LieART`Private`SingleOrProductIrrepQ)] ];

AlgebraClass[LieART`Private`productWeight_ProductWeight] := 
  Map[AlgebraClass, List @@ LieART`Private`productWeight];

Algebra[LieART`Private`productIrrep_ProductIrrep] := 
  ProductAlgebra @@ Map[Algebra, List @@ LieART`Private`productIrrep];
Algebra[LieART`Private`productWeight_ProductWeight] := 
  ProductAlgebra @@ Map[Algebra, List @@ LieART`Private`productWeight];
Algebra[LieART`Private`irrepTimes_IrrepTimes] := 
  Algebra@Last[LieART`Private`irrepTimes];
Algebra[LieART`Private`irrepSum_IrrepPlus] := 
  Map[Algebra, List @@ LieART`Private`irrepSum];

SetAttributes[ProductAlgebra, {Flat}];

Irrep[ Algebra[f_][n_Integer?Positive] ][lbl__] /; (n == Length[{lbl}]) :=
  Irrep[f][lbl];
Irrep[g : ProductAlgebra[l__] ][lbl__] /; (Rank[g] == Length[{lbl}]) :=
  ProductIrrep@@MapThread[
    Irrep[AlgebraClass@#1] @@ #2 &, 
    {{l}, TakeList[{lbl}, Rank/@{l}]}
  ];

Weight[ Algebra[f_][n_Integer?Positive] ][lbl__] /; (n == Length[{lbl}]) :=
  Weight[f][lbl];
Weight[g : ProductAlgebra[l__] ][lbl__] /; (Rank[g] == Length[{lbl}]) :=
  ProductWeight@@MapThread[
    Weight[AlgebraClass@#1] @@ #2 &, 
    {{l}, TakeList[{lbl}, Rank/@{l}]}
  ];

Orbit[ ProductWeight[LieART`Private`w__] ] :=
  Flatten@Outer[ ProductWeight, Sequence@@Map[Orbit, {LieART`Private`w}] ];

DominantQ[ ProductWeight[LieART`Private`w__] ] :=
  AllTrue[{LieART`Private`w}, DominantQ];

AlphaBasis[ ProductWeight[LieART`Private`w__] ] :=
  Apply[ProductWeight, AlphaBasis /@ {LieART`Private`w}];
OmegaBasis[ ProductWeight[LieART`Private`w__] ] :=
  Apply[ProductWeight, OmegaBasis /@ {LieART`Private`w}];

Times[LieART`Private`f_, ProductWeight[LieART`Private`w: ((WeightAlpha | Weight)[_][__])..] ] ^:=
  Apply[ProductWeight, LieART`Private`f*{LieART`Private`w}];
Plus[ ProductWeight[LieART`Private`w1 : (WeightAlpha[_][__])..], ProductWeight[LieART`Private`w2 : (WeightAlpha[_][__])..] ] ^:=
  Apply[ProductWeight, {LieART`Private`w1} + {LieART`Private`w2}] /; SameQ[Length@{LieART`Private`w1}, Length@{LieART`Private`w2}];
Plus[ ProductWeight[LieART`Private`w1 : (Weight[_][__])..], ProductWeight[LieART`Private`w2 : (Weight[_][__])..] ] ^:=
  Apply[ProductWeight, {LieART`Private`w1} + {LieART`Private`w2}] /; SameQ[Length@{LieART`Private`w1}, Length@{LieART`Private`w2}];

WeylDimensionFormula[ (List | ProductAlgebra)[LieART`Private`algebras__] ] :=
  Module[{LieART`Private`ranks, LieART`Private`args, LieART`Private`func},
    LieART`Private`ranks = Rank /@ {LieART`Private`algebras};
    LieART`Private`args = Map[ToExpression[ "a" <> ToString[#1] ] &, 
      Range@Total[LieART`Private`ranks] ];
    LieART`Private`func = Times @@ MapThread[
      WeylDimensionFormula[#1] @@ #2 &, 
      {{LieART`Private`algebras}, TakeList[LieART`Private`args, LieART`Private`ranks]}
    ];
    Function[Evaluate@LieART`Private`args, Evaluate@LieART`Private`func]
  ];

(*PACKAGE STARTS HERE*)

Unprotect["LieARTCharacters`*"];
ClearAll["LieARTCharacters`*"];


BeginPackage["LieARTCharacters`", {"LieART`"}];


ToDynkinLabel::usage = "";
DominantWeightOrder::usage = "";
HighestWeights::usage = "";
HighestWeightsFrom::usage = "";
\[Chi]::usage = "";
CharacterDecomposition::usage = "";
MonomialCoefficient::usage = "";
ToCharacterGeneratorFunction::usage = "";
WeylGroupOrder::usage = "";
FugacityMap::usage = "";

StepMonitorFunction::usage = "";


$SaveCharacterDefinitions = True;


Begin["`Private`"];


DynkinLabelQ[n__Integer?NonNegative] = True;
DynkinLabelQ[_] = False;
(*SetAttributes[DynkinLabelQ, {ReadProtected, Protected}];*)


AlgebraQ[ Algebra[A | B | C | D][_Integer] ] = True;
AlgebraQ[E6 | E7 | E8 | G2 | F4] = True;
AlgebraQ[_] = False;
(*SetAttributes[AlgebraQ, {ReadProtected, Protected}];*)


AlgebraClassQ[A | B | C | D] = True;
AlgebraClassQ[E6 | E7 | E8 | G2 | F4] = True;
AlgebraClassQ[_] = False;
(*SetAttributes[AlgebraClassQ, {ReadProtected, Protected}];*)


ProductAlgebraQ[ ProductAlgebra[__?AlgebraQ] ] = True;
ProductAlgebraQ[_] = False;
(*SetAttributes[ProductAlgebraQ, {ReadProtected, Protected}];*)


IrrepQ[ Irrep[A | B | C | D][__?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[E6][(Repeated[_, {6}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[E7][(Repeated[_, {7}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[E8][(Repeated[_, {8}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[F4][(Repeated[_, {4}])?DynkinLabelQ] ] = True;
IrrepQ[ Irrep[G2][(Repeated[_, {2}])?DynkinLabelQ] ] = True;
IrrepQ[_] = False;
(*SetAttributes[IrrepQ, {ReadProtected, Protected}];*)


ProductIrrepQ[ ProductIrrep[__?IrrepQ] ] = True;
ProductIrrepQ[_] = False;
(*SetAttributes[ProductIrrepQ, {ReadProtected, Protected}];*)


SingleOrProdIrrepQ[_?IrrepQ] = True;
SingleOrProdIrrepQ[_?ProductIrrepQ] = True;
SingleOrProdIrrepQ[_] = False;
(*SetAttributes[SingleOrProdIrrepQ, {ReadProtected, Protected}];*)


IrrepTimesQ[ HoldPattern[IrrepTimes][_, _?SingleOrProdIrrepQ] ] = True;
IrrepTimesQ[_] = False;
(*SetAttributes[IrrepTimesQ, {ReadProtected, Protected}];*)


IrrepPlusQ[ IrrepPlus[s: (_?IrrepTimesQ | _?SingleOrProdIrrepQ) ..] ] :=
  SameQ @@ Algebra@IrrepPlus[s];
IrrepPlusQ[_] = False;
(*SetAttributes[IrrepPlusQ, {ReadProtected, Protected}];*)


WeightQ[ (WeightAlpha | Weight)[A | B | C | D][__] ] = True;
WeightQ[ (WeightAlpha | Weight)[E6][(Repeated[_, {6}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[E7][(Repeated[_, {7}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[E8][(Repeated[_, {8}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[F4][(Repeated[_, {4}])] ] = True;
WeightQ[ (WeightAlpha | Weight)[G2][(Repeated[_, {2}])] ] = True;
WeightQ[_] = False;
(*SetAttributes[WeightQ, {ReadProtected, Protected}];*)


ProductWeightQ[ ProductWeight[__?WeightQ] ] = True;
ProductWeightQ[_] = False;
(*SetAttributes[ProductWeightQ, {ReadProtected, Protected}];*)


SingleOrProdWeightQ[_?WeightQ] = True;
SingleOrProdWeightQ[_?ProductWeightQ] = True;
SingleOrProdWeightQ[_] = False;
(*SetAttributes[SingleOrProdIrrepQ, {ReadProtected, Protected}];*)


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


ToDynkinLabel[ ProductIrrep[ir__?IrrepQ] ] := 
  Map[ToDynkinLabel, {ir}];
ToDynkinLabel[ Irrep[_][ns__?DynkinLabelQ] ] := {ns};
SetAttributes[ToDynkinLabel, {ReadProtected, Protected}];


\[Chi][{lbl__?DynkinLabelQ}] := 
  \[Chi][A, {lbl}];
\[Chi][g_?AlgebraQ, {lbl__?DynkinLabelQ}] /; (!SameQ[Length@{lbl}, Rank@g]) :=
  Null /; Message[\[Chi]::errmatchrk, g, {lbl}];
\[Chi][g: (_?AlgebraQ | _?AlgebraClassQ), {lbl__?DynkinLabelQ}] := 
  \[Chi][ Irrep[AlgebraClass@g][lbl] ];
\[Chi][w: (WeightAlpha[g_][lbl__]) ] :=
  \[Chi][ OmegaBasis@w ];
\[Chi][ Weight[g_][lbl__] ] /; (!IrrepQ[ Irrep[g][lbl] ]) :=
  Null /; Message[\[Chi]::errirrep, Irrep[g][n] ];
\[Chi][ Weight[g_][lbl__] ] :=
  \[Chi][ Irrep[g][lbl] ];
\[Chi][ ProductWeight[w__] ] /; (!ProductIrrepQ[ProductIrrep @@ ToIrrep@OmegaBasis@{w}]) :=
  Null /; Message[\[Chi]::errirrep, ProductIrrep @@ ToIrrep@OmegaBasis@{w}] ;
\[Chi][ ProductWeight[w__] ] :=
  \[Chi][ ProductIrrep @@ ToIrrep@OmegaBasis@{w} ];
\[Chi][rep_?IrrepQ] :=
  Module[{ws, f, func},
    ws = MapAt[Apply[List], WeightSystemWithMul[rep], {All, 1}];
    f = Total[(#2* Apply[Times, Array[Slot, Rank@rep]^#1] &) @@@ ws];
    func = Function[Evaluate@f];
    If[$SaveCharacterDefinitions,
      Unprotect[ \[Chi] ];
      \[Chi][ rep ] = Evaluate[func];
      Protect[ \[Chi] ];
    ];
    Return[func];
  ];
\[Chi][{gs: Repeated[_?AlgebraQ, {2, Infinity}]}, lbl: {{__?DynkinLabelQ} ..}] :=
  \[Chi][ProductAlgebra[gs], lbl]
\[Chi][g_?ProductAlgebraQ, lbl: {{__?DynkinLabelQ} ..}] /; (!SameQ[Length@g, Length@lbl]) :=
  Null /; Message[\[Chi]::errmatchcomp, g, lbl];
\[Chi][g_?ProductAlgebraQ, lbl: {{__?DynkinLabelQ} ..}] /; (!SameQ[Rank/@List@@g, Length/@lbl]) :=
  Null /; Message[\[Chi]::errmatchrk, g, lbl];
\[Chi][g_?ProductAlgebraQ, lbl: {{__?DynkinLabelQ} ..}] :=
  \[Chi][ MapThread[Irrep[AlgebraClass@#1]@@#2 &, {List@@g, lbl}] ];
\[Chi][{reps__?IrrepQ}] :=
  \[Chi][ ProductIrrep[reps] ];
\[Chi][prodRep_?ProductIrrepQ] :=
  Module[{reps, rnks, f, func},
    reps = List @@ prodRep;
    rnks = Rank /@ reps;
    f = Times @@ MapThread[
      \[Chi][#1] @@ Array[Slot, #2, #3] &,
      {reps, rnks, Accumulate[{1, Splice@Most@rnks}]}
    ];
    func = Function[Evaluate@f];
    Return[func];
  ];
\[Chi][repSum_IrrepPlus?IrrepPlusQ] :=
  Module[{f, func, rnk},
    rnk = Rank[repSum];
    f = Sum[\[Chi][r] @@ Array[Slot, rnk], {r, List@@repSum}];
    func = Function[Evaluate@f];
    Return[func];
  ];
\[Chi][repSum_IrrepPlus] := 
  Null /; Message[\[Chi]::errirrepsum];
\[Chi][repTimes_IrrepTimes?IrrepTimesQ] :=
  Module[{rnk, c, rep, f, func},
    rnk = Rank[repTimes];
    {c, rep} = List @@ repTimes;
    f = c * (\[Chi][rep] @@ Array[Slot, rnk]);
    func = Function[Evaluate@f];
    Return[func];
  ];
\[Chi]::errmatchrk = "The rank of the algebra `1` does not match dimension of representation `2`."
\[Chi]::errmatchrksum = "The rank of the irrep sum does not match for all summands."
\[Chi]::errirrep = "`1` is not a valid irrep."
\[Chi]::errirrepsum = "The sum is not a valid representation. Check each factor is a irrep of the same algebra."
SetAttributes[\[Chi], {ReadProtected, Protected}];


DominantWeightOrder[w1_?DominantQ, w2_?DominantQ] /; (!SameQ[Algebra@w1, Algebra@w2]) :=
  Null /; Message[DominantWeightOrder::algerr];
DominantWeightOrder[w1_?DominantQ, w2_?DominantQ] :=
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
DominantWeightOrder[_, _] := Null /; Message[DominantWeightOrder::argerr];
DominantWeightOrder::algerr = "Algebras of the dominant weights do not match.";
DominantWeightOrder::argerr = "Arguments are not dominant weights."


HighestWeights[ls : {__?WeightQ} | {__?ProductWeightQ}] /; Not[SameQ @@ Map[Algebra, ls] ] := 
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
  Null /; Message[HighestWeightsFrom::lenerr, g, {vars}];
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
  Module[{gs, rk, v0, varsByRk, flattenA, foldF, coef, W},
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


Options[CharacterDecomposition] = {MaxIterations -> Automatic, StepMonitorFunction -> None};
CharacterDecomposition[{gs__?AlgebraQ}][expr_, {vars__}, opts : OptionsPattern[CharacterDecomposition] ] :=
  CharacterDecomposition[expr, {vars}, ProductAlgebra[gs], opts];
CharacterDecomposition[g : (_?AlgebraQ | _?AlgebraClassQ | _?ProductAlgebraQ)][expr_, {vars__}, 
    opts : OptionsPattern[CharacterDecomposition] ] := 
  CharacterDecomposition[expr, {vars}, g, opts];
CharacterDecomposition[expr_, {vars__}, g: (_?AlgebraQ | _?ProductAlgebraQ), 
    opts : OptionsPattern[CharacterDecomposition] ] /; (UnsameQ[Length[{vars}], Rank@g]) :=
  Null /; Message[CharacterDecomposition::lenerr, g, {vars}];
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
      AppendTo[hws, ws];
      PrependTo[chars, Thread[ws -> coefs] ];
      stepF[e, Reverse@chars, ws];
      Expand[e - Map[(\[Chi][#][vars] &), ws] . coefs]
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


MonomialCoefficient[e_, {v__}, {n__?NumericQ}] /; (UnsameQ[ Length[{v}], Length[{n}] ]) := 
  Null /; Message[MonomialCoefficient::lenerr, {v}, {n}] ;
MonomialCoefficient[e_, {v__}, {n__?NumericQ}] := 
  Fold[
    Function[{x, pair}, Coefficient[x, First@pair, Last@pair] ],
    e, 
    Transpose[{{v}, {n}}]
  ];
MonomialCoefficient::lenerr = "Length of `1` and `2` do not match.";
SetAttributes[MonomialCoefficient, {ReadProtected, Protected}];


ToCharacterGeneratorFunction[mu:_Symbol][a_Association] :=
  ToCharacterGeneratorFunction[a, Array[mu, First[Rank /@ Keys@a, 0] ] ];
ToCharacterGeneratorFunction[{vars__}][a_Association] :=
  ToCharacterGeneratorFunction[a, {vars}];
ToCharacterGeneratorFunction[<||>, _] := 0;
ToCharacterGeneratorFunction[a_Association, {vars___}] := 
  Total@KeyValueMap[#2 Apply[Times, Flatten[{vars}]^Flatten@ToDynkinLabel@#1] &, a];
SetAttributes[ToCharacterGeneratorFunction, {ReadProtected, Protected}];


FugacityMap[g_?AlgebraQ, gsub : (_?AlgebraQ | ProductAlgebra[(_?AlgebraQ | U1) ..])] :=
  Enclose[Module[{P, map},
    P = ProjectionMatrix[g, gsub];
    ConfirmAssert[MatchQ[P, _?MatrixQ], Message[FugacityMap::nosubalg, g, gsub] ];
    map = Times @@@ (Array[Subscript[\[FormalZ], #] &, Length@#]^# &) /@ Transpose[P];
    Thread[Array[Subscript[\[FormalZ], #] &, Length@map] -> map]
  ], Null &];
FugacityMap::nosubalg = "`1` does not have `2` as a subalgebra. Try changing the order in `2`.";
SetAttributes[FugacityMap, {ReadProtected, Protected}];


End[];


EndPackage[];

