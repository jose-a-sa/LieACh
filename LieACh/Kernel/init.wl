
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
    res = If[NoneTrue[available, 
    	Apply[And, GreaterEqual @@@ Transpose@PadRight[ToExpression@StringSplit[{#1, minVersion}, "."]]] &], 
      Check[installLieART[minVersion], 
      Print["Failed to install LieART"]; Return@$Failed]
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


$LieARTmodFile = FileNameJoin[{DirectoryName[$InputFileName, 2], "LieARTMod.wl"}];
If[ !FileExistsQ[$LieARTmodFile],
  tAbort["Failed to find LieARTMod.wl"]; Abort[]
];

(* LieART install/download *)
getLieART[];
Remove[{getLieART, installLieART}];

(* LieART modding *)
Import[$LieARTmodFile];
Remove[{$LieARTmodFile}];


Get["LieACh`LieACh`"]
