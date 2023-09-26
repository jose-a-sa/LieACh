#!/usr/bin/env wolframscript

$appName = "LieARTCharacters";

tAbort[str_] := (Print["ABORTING: ", Style[str, Red, Bold]]; Quit[])
If[$VersionNumber < 12.3, printAbort["Mathematica 12.3 or later required."]]

$dir = Which[
    $InputFileName =!= "", DirectoryName[$InputFileName],
    $Notebooks, NotebookDirectory[],
    True, printAbort["Cannot determine script directory."]
];

If[Not@DirectoryQ[$appName], 
	printAbort["Application directory not found."]
];

Check[
  Quiet[PacletDirectoryAdd[$appName], PacletDirectoryAdd::expobs];
  Needs[$appName <> "`"],
  printAbort["Cannot add paclet directory and load package."]
];

If[AbsoluteFileName[$appName] =!= Information[PacletObject[$appName], "Location"],
  printAbort["Wrong paclet loaded."]
];


ClearAll[generateLogo];
generateLogo[algebra_: LieART`E6, thick_:0.005, opa_:0.8, size_Integer: 128] :=
  Module[{delta, eig, roots, grouped, ig, jg, xx, yy, eg, ln, gp, normK, colorFn, d},
    delta = List @@@ OrthogonalSimpleRoots[algebra];
    eig = Simplify @ ToRadicals @ Eigenvectors[CartanMatrix[algebra]] // Last;
    roots = RootSystem[algebra] // OrthogonalBasis // MapApply[List];
    grouped = AssociationThread[Range[Length @ delta], delta];
    {ig, jg} = FindGraphPartition @ RelationGraph[Dot[Lookup[grouped,
       #1], Lookup[grouped, #2]] == 0&, Keys[grouped] ];
    xx = Total[eig[[ig]] delta[[ig]]] // N;
    yy = Total[eig[[jg]] delta[[jg]]] // N;
    xx = Normalize[xx];
    yy = yy - Dot[xx, yy] xx;
    yy = Normalize[yy];
    eg = UndirectedEdge @@@ Select[Subsets[roots, {2}], Dot[{1, -1}.#, {1, -1}.#] == 4&];
    ln = MapAt[{#.xx, #.yy} &, Line@*List @@@ eg, {All, 1, All}];
    d = Chop @ TransformedRegion[
      BoundingRegion[Map[{#.xx, #.yy}&, roots], "MinDisk"], 
      1.1 # &
    ];
    colorFn[l_] := Max[Norm /@ Identity @@ l];
    ln = ReverseSortBy[RegionMeasure]@Select[ln, 
      And[Not@PossibleZeroQ@Chop@colorFn[#], Not@PossibleZeroQ@RegionMeasure@#]&
    ];
    gp = Map[colorFn, ln];
    normK[x_] = 0.001 + 0.998 ((x - Min @ gp) / (Max @ gp - Min @ gp));
    Graphics[{
      {DropShadowing[{0, 0}, 5], FaceForm[White], d}, 
      Map[{ColorData["Rainbow"][0.05 + 0.75 normK[colorFn @ #1]], 
        Thickness[thick], Opacity[opa], #1}&, ln]
      }, 
      PlotRangePadding -> Scaled[.05], 
      ImageSize -> {size, size}
    ]
  ];
MapThread[
	Export[
		FileNameJoin[{AbsoluteFileName[$appName], "icon", "icon-"<>ToString[#1]<>".svg"}], 
		generateLogo[E6, #2, 0.8], 
		ImageSize -> {#1, #1}
	] &,
	{{64, 128, 256, 512}, 
	{0.005, 0.004, 0.003, 0.002},
	{0.85, 0.8, 0.75, 0.70}}
];


date = DateString[{"Year", "Month", "Day"}];
time = DateString[{"Hour24", "Minute", "Second"}];

template = StringTemplate[
	Import[FileNameJoin[{$appName, $appName <> ".wl"}], "String"],
    Delimiters -> "%%"
];

versionData = <|
  "version" -> Information[PacletObject[$appName], "Version"],
  "mathversion" -> Information[PacletObject[$appName], "WolframVersion"],
  "date" -> DateString[{"MonthName", " ", "DayShort", ", ", "Year"}]
|>;

allSymbols = Join[ Names[$appName <> "`*"], Names["LieART`*"] ];
Unprotect /@ allSymbols;
ClearAll /@ allSymbols;
Remove /@ allSymbols;


Needs["PacletTools`"];

$buildDir = "build";
If[Not@DirectoryQ[$buildDir],
	CreateDirectory[$buildDir, CreateIntermediateDirectories -> True]
];

PacletDocumentationBuild[AbsoluteFileName[$appName], $buildDir];

Map[
	Block[{newPath, newDir},
		newPath = FileNameJoin[{Directory[], $buildDir, FileNameDrop[#, Length@FileNameSplit@Directory[]]}];
		newDir = FileNameDrop[newPath, -1];
		If[Not@DirectoryQ@newDir,
			CreateDirectory[newDir, CreateIntermediateDirectories -> True]
		];
		Echo[CopyFile[#, newPath, OverwriteTarget -> True], #] ;
	] &,
	DeleteCases[_?DirectoryQ]@Select[
		FileNames["*", AbsoluteFileName[$appName], Infinity], 
		FreeQ["Documentation" | ".DS_Store"]@*FileNameSplit
	]
];

Echo@CreatePacletArchive[FileNameJoin[{Directory[], $buildDir, $appName}], $buildDir];



