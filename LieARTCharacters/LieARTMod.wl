(* LieART modding *)

If[$Notebooks,
  SetOptions[EvaluationNotebook[], 
    CommonDefaultFormatTypes -> {"Output" -> StandardForm}
  ];
];

Algebra[U][n_Integer?(GreaterThan[1])] := 
  ProductAlgebra[Algebra[A][n], Algebra[U][1] ];


Rank[ Irrep[LieART`U][LieART`Private`label_] ] := 1;
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


Algebra[ Irrep[LieART`U][LieART`Private`label__] ] := 
  Algebra[U][Length[{LieART`Private`label}]]
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
Algebra::irrplusdiff = "IrrepPlus contains irreps of different algebras `1`.";
SetAttributes[ProductAlgebra, {Flat}];


Irrep[ Algebra[LieART`Private`c_][LieART`Private`n_Integer?Positive] ][LieART`Private`label__] /; 
    (LieART`Private`n == Length[{LieART`Private`label}]) :=
  Irrep[LieART`Private`c][LieART`Private`label];
Irrep[LieART`Private`g : ProductAlgebra[LieART`Private`a__] ][LieART`Private`label__] /; 
    (Rank[LieART`Private`g] == Length[{LieART`Private`label}]) :=
  ProductIrrep@@MapThread[
    Irrep[AlgebraClass@#1] @@ #2 &, 
    {{LieART`Private`a}, TakeList[{LieART`Private`label}, Rank/@{LieART`Private`a}]}
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


IrrepPlus[{l : (ProductIrrep[__?IrrepQ] ..)}] /; (Apply[SameQ, Algebra /@ {l}]) :=
  IrrepPlus[l];
IrrepPlus[{l : (ProductIrrep[__?IrrepQ, Irrep[U][_Integer] ] ..)}] /; (Apply[SameQ, Algebra /@ {l}]) :=
  IrrepPlus[l];


WeylDimensionFormula[ (List | ProductAlgebra)[LieART`Private`algebras__] ] :=
  Module[{ranks, args, func},
    ranks = Rank /@ {LieART`Private`algebras};
    args = Map[
      ToExpression[ "a" <> ToString[#1] ] &, 
      Range@Total[ranks]
    ];
    func = Times @@ MapThread[
      WeylDimensionFormula[#1] @@ #2 &, 
      {{LieART`Private`algebras}, TakeList[args, ranks]}
    ];
    Function[Evaluate@args, Evaluate@func]
  ];

