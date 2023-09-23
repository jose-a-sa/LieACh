(* Wolfram Language Init File *)

getLieART[]:=
  Module[{available, minVersion, res, setStdForm},
    setStdForm[] := If[$Notebooks,
      SetOptions[EvaluationNotebook[], 
        CommonDefaultFormatTypes -> {"Output" -> StandardForm}
      ];
    ];
    If[AnyTrue[$Packages, StringMatchQ["LieART`"] ],
      setStdForm[]; Return[Null]
    ];
    minVersion = "2.1.0";
    available = Select[
    	Map[ #["Version"] &, PacletFind["LieART"] ],
    	StringMatchQ[Repeated[(DigitCharacter ..) ~~ ".", {1, Infinity}] ~~ (DigitCharacter ..)]
    ];
    If[NoneTrue[available, 
    	Apply[And, GreaterEqual @@@ Transpose@PadRight[ToExpression@StringSplit[{#1, minVersion}, "."]]] &], 
      Check[installLieART[minVersion], Return@$Failed]
    ];
    res = Quiet@Needs["LieART`"];
    setStdForm[];
    res
  ];

installLieART[version_String] := 
  Module[{download, tempDir, target, pacletObj, paclet, res},
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
(* no need to Unprotect *)


Rank[LieART`Private`productAlgebra_ProductAlgebra] := 
  Total[Rank /@ (List @@ LieART`Private`productAlgebra)];
Rank[LieART`Private`productIrrep_ProductIrrep] := 
  Total[Rank /@ (List @@ LieART`Private`productIrrep)];
Rank[LieART`Private`productWeight_ProductWeight] := 
  Total[Rank /@ (List @@ LieART`Private`productWeight)];
Rank[LieART`Private`irrepSum_IrrepPlus] :=
  Module[{gs},
    gs = Union@Map[Algebra, List @@ LieART`Private`irrepSum];
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
  First@Union@Map[Algebra, List @@ LieART`Private`irrepSum] /;
  Length@Union@Map[Algebra, List @@ LieART`Private`irrepSum] == 1;
Algebra[LieART`Private`irrepSum_IrrepPlus] :=
  Null /; Message[Algebra::irrplusdiff, Union@Map[Algebra, List @@ LieART`Private`irrepSum]];
Algebra::irrplusdiff = "IrrepPlus contains irreps of different algebras `1`."

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


Get["LieARTCharacters`LieARTCharacters`"]
