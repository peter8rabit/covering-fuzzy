
$fuzzyProjectPath = DirectoryName@$InputFileName

Get[#, CharacterEncoding -> "UTF8"]&/@Select[$InputFileName != # &]@FileNames["*.m", $fuzzyProjectPath, Infinity];

(*DEF:シンボルｆに全体集合がXの[0,1]から一様なランダム値を持つ集合関数を生成する*)
SetAttributes[randomSetFunction, HoldFirst]
randomSetFunction[f_Symbol, X_List,negativeQ_:False] := Module[{},
  ClearAll@f;
  f[{}] = 0;
  Function[x,
    f[x] = If[negativeQ,RandomReal[{-1,1}],RandomReal[]];
  ] /@ Subsets[X, {1, Length@X}];
]

(*DEF:｜A｜/｜X｜+ 1 /｜X｜*N(0,１)*)
(*DEF:<|"a" -> 3, "b" -> 1, "c" -> 4|>=>{"c", "a", "b"}*)
permutation[x_] := Keys@ReverseSort@KeySort@x

(*calcWalk@{0.2, 0.8, 0.3} => {{2}, {2, 3}, {1, 2, 3}}*)
(*calcWalk[x_List] :=
    Reverse@Map[Sort]@
        NestList[Most,
          Keys@ReverseSort@
              KeySort@AssociationThread[ Range@Length@x -> Ordering@x], Length@x - 1]*)
calcWalk[x_List] :=With[{X = Range@Length@x},
  Function[xs, Map[Sort@xs[[;; #]] &, X]]@
      Keys@ReverseSort@AssociationThread[X -> x]
]


(*DEF:Walkじゃないパラメータの登場比率*)
parameterFrequencies[walks_List] := Module[{assc, g},
  assc = KeySort@Counts@Flatten[walks, 1];
  Map[(g[#] = 0) &, Subsets@walks[[1, -1]]];
  KeyValueMap[(g[#1] = N[#2/total]) &, assc];
  g
]

walkCentricShapleys[u_, supproteds_, X_] := Module[{assc},
  assc = AssociationMap[Function[x,
    Total@
        Map[1/(Length@X*Binomial[Length@X - 1, Length@#])*
            Boole[MemberQ[supporteds, #] &&
                MemberQ[supporteds, Append[x]@#]]*(u@Union[#, {x}] -
            u@#) &, Subsets@DeleteCases[X, x]]
  ], X];
  Map[#/Total@assc &, assc]
]



Clear@hasseDiagram
Options[hasseDiagram] = {"X" -> Missing[]}
hasseDiagram[trainset_List:Missing[],f_:Missing[],OptionsPattern[]] := Module[
  {
    xs
    ,ys
    ,inputs
    ,X
    ,walks
    ,circlePrims
    ,walkPrims
    ,y
    ,x
    ,auxFuzzyPos
    ,auxWalkWeight
    ,auxWalkWeightRescaled
  },
  inputs = If[MissingQ@trainset,{},Keys@trainset];
  ys = N@Transpose@Map[Rescale]@Transpose@inputs;
  X = If[MissingQ@OptionValue["X"],Range@Length@First@inputs,OptionValue["X"]];
  walks = Map[Prepend[{}]@calcWalk@# &]@ys;

  circlePrims = Last@Last@Reap@For[y = 1, y <= Length@X + 1, y++,
    xs = Subsets[X, {y - 1}];
    For[x = 1, x <= Length@xs, x++,
      auxFuzzyPos[xs[[x]]] = {x/( Length@xs + 1), y/( Length@X + 1)};
      Sow@{
        If[Not@MissingQ@f && f@xs[[x]] < 0, Red, Nothing],
        If[Not@MissingQ@f,Text[Floor[f@xs[[x]],0.01],Scaled[auxFuzzyPos[xs[[x]]]]],Nothing],
        Circle[Scaled[auxFuzzyPos[xs[[x]]]],
          If[Not@MissingQ@f, Abs@f@xs[[x]]/10, 0.05]]
      }
    ]
  ];

  Function[
    n, (Evaluate[auxWalkWeight @@ #] = 0) & /@
      Tuples[{Subsets[X, {n}], Subsets[X, {n + 1}]}]] /@
      Range[0, Length@X - 1];

  Function[w,
    BlockMap[(auxWalkWeight[First@#, Last@#] =
        auxWalkWeight[First@#, Last@#] + 1) &, w, 2, 1]] /@ walks;

  MapThread[
    Function[{key, val},
      key /. _[_[a_, b_]] :> (auxWalkWeightRescaled[a, b] =
          val)], {Keys@DownValues@auxWalkWeight,
    N@Rescale@Values@DownValues@auxWalkWeight}];

  walkPrims = Function[w,
    BlockMap[
      If[auxWalkWeight[First@#, Last@#] >
          0, {Thickness[auxWalkWeightRescaled @@ #/100],
        Line[{Scaled@auxFuzzyPos[First@#],
          Scaled@auxFuzzyPos[Last@#]}]}, Nothing] &, w, 2, 1]
  ] /@ walks;

  Graphics[{circlePrims, walkPrims}]
]

allAlgebra[xs_List] := Select[Subsets@Subsets@xs,
  Function[subset,
    (*STEP:定義1*)
    MemberQ[subset, {}] &&
        (*STEP:定義2*)
        AllTrue[subset, MemberQ[subset, Complement[xs, #]]&] &&
        (*STEP:定義3*)
        AllTrue[Union@@@Subsets[subset, {2}]//Union, MemberQ[subset, #]&]
  ]
]

(*TODO:メビウスの値も出力させる*)
binaryClassificationModel["Grabisch",datasetRescaled_]:=Module[
  {
    trainset
    ,testset
    ,u
    ,n
    ,X
    ,T0
    ,T1
    ,confidence
    ,objective
    ,sols
    ,comp
  },
  {trainset, testset} = ResourceFunction["RatioPartition"][RandomSample@datasetRescaled, {70, 30}];
  X = Keys@Keys@First@Values@datasetRescaled;

  u[0][{}] = 0;
  u[1][{}] = 0;
  u[0][X] = 1;
  u[1][X] = 1;

  T0 = Map[Keys]@Cases[trainset, HoldPattern[_ -> 0 | False]];
  T1 = Map[Keys]@Cases[trainset, HoldPattern[_ -> 1 | True]];

  (*STEP:最適化*)
  confidence[assc_, label_] := choquet[assc, u[label], X];
  objective = Total@Map[(confidence[#, 0] - confidence[#, 1] - 1)^2&, T0] + Total@Map[(confidence[#, 1] - confidence[#, 0] - 1)^2&, T1];
  sols = QuadraticOptimization[objective, monotoneConditions[u[0], X] ~ Join ~ monotoneConditions[u[1], X] , Flatten[{u[0]@#, u[1]@#}& /@ Subsets[X, {1, Length@X - 1}]]];
  Map[(Evaluate@Keys@# = Values@#)& ]@sols;

  (*STEP:指標計算*)
(*  comp = Map[{confidence[#, 0], confidence[#, 1], If[confidence[#, 0] <= confidence[#, 1], 1, 0], #["label"]}&, testset];*)

(*  Return@<|"test" -> CountsBy[comp, #[[3]] == Last@#&], "measure" -> u, "testset" -> testset, "confidence" -> confidence, "result" -> Counts@comp[[All, 3 ;; 4]]|>;*)
  Return@<|"measure" -> u, "confidence" -> confidence|>;
]



(*DEF:*)
isQuasiSubset[s1_List, s2_List] := And @@ Map[Function[s1x, Or @@ Map[SubsetQ[#, s1x] &, s2]], s1]
(*DEF:*)
isQuasiEqual[s1_List, s2_List] := isQuasiSubset[s1, s2] && isQuasiSubset[s2, s1]

focus[u_, domainNum_ : 3] := Select[toMobius[u, #] != 0 &]@Subsets[Range@domainNum]


(*choquet[f_,u_,X_,"version2"]:=Module[
  {
    assc
  },
  assc = Sort@AssociationThread[X -> f/@X];
  Total@Map[
    Function[i, (assc[[i]] - If[i - 1 == 0, 0, assc[[i - 1]]])*u[Sort@Keys@assc[[i ;;]]]]
    , Range@Length@X
  ]
]*)



(*DEF:dsは{{...}...}とする*)
correlationMatrixPlot[ds_Dataset]:=correlationMatrixPlot@Values@ds
correlationMatrixPlot[ds_List]:=Module[{corr,ticks,matplot1},
  corr=N@Correlation@ds;
  ticks={{Table[{i,"row "<>ToString[i]},{i,1,Length@corr}],None},{None,Table[{i,"column "<>ToString[i]},{i,1,Length@corr}]}};
  matplot1=MatrixPlot[corr,Epilog->{Black,MapIndexed[Text[#1,Reverse[#2-1/2]]&,Reverse[corr],{2}]},Mesh->True,ColorFunction->ColorData[{"Temperature","Reverse"}],FrameTicks->ticks]
]



(* => メビウス計画行列*)
(*Coveringがあっても行列の大きさは2^|X|-1*)
toMobiusMatrix[designMatrix_List, X_List, covering_ : Missing[]] := Module[
  {
    m,u
  },
  m[{}] = 0;
  Map[
    Function[x,
      toSubsetVector[#, m, X]&@(
        choquet[x[[#]] &, u, X] /. u[A_] :>
            Expand@If[MissingQ@covering, fromMobius[m, A], fromCoveringMobius[m, covering, A]]
      )
    ],
    designMatrix
  ]
]

(*DEF:メビウス測度から包除被覆を計算する*)
calcCovering[m_, X_] := maximalFamily@Complement[Subsets[X],Keys@Select[# == 0 &]@AssociationMap[m, Subsets[X]]]


fuzzyRegression[ds_]:=Module[
  {
    X = Range@Length@Keys@First@ds,
    u,
    objectFunction,
    monoconds,
    sols,
    params,
    residual
  },

  u[{}] = 0;

  objectFunction = Total@Map[Function[x, (Values@x - choquet[Keys[x][[#]] &, u, X])^2], ds];
  monoconds = monotoneConditions[u, X];

  sols = QuadraticOptimization[
    objectFunction,
    monoconds,
    u /@ Subsets[X, {1, Length@X}]
  ];

  Map[(Evaluate@Keys@# = Values@#) &, sols];

  params = AssociationMap[u, Subsets[X]];

  residual = Total@Map[Function[x, (Values@x - choquet[Keys[x][[#]] &, u, X])^2], ds];

  Return@<|
    "measure"->params,
    "totalSquareResidual"->residual
    (*    ,*)
    (*    "AIC" -> Length@ds*Log[residual/Length@ds] + 2*(Length@heredityFamily@covering - 1),*)
    (*    "BIC" -> Length@ds*Log[residual/Length@ds] + (Length@heredityFamily@covering - 1)*Log[Length@ds]*)
  |>
]




coveringFuzzyRegression[trainset_List,covering_List]:= Module[
  {
    X = Range@Length@Keys@First@trainset,
    u,
    objectFunction,
    monoconds,
    sols
    ,
    params,
    totalSquareResidual,
    sse,
    A,
    MM,
    i,
    tvalues,
    M,
    posAssc,
    posAssc2,
    shrinkedM,
    mobiusParams
  },

  u[{}] = 0;

  Function[A,
    u[A] = fromCovering[u, covering, A]
  ] /@ Complement[Subsets[X], heredityFamily@covering];

  objectFunction = Total@Map[Function[x, (Values@x - choquet[Keys[x][[#]] &, u, X])^2], trainset];
  monoconds = monotoneConditions[u, X];

  sols = QuadraticOptimization[
    objectFunction,
    monoconds,
    u /@ DeleteCases[{}]@heredityFamily@covering
    ,Method -> "CSDP"
(*    ,MaxIterations->2500*)
  ];

  Map[(Evaluate@Keys@# = Values@#) &, sols];

  params = DownValues@u /. HoldPattern[_[u[xs_]] :> _] :> xs -> u[xs] // Association;
  mobiusParams = toMobiusMeasure[params, X];
  totalSquareResidual = Total@Map[Function[x, (Values@x - choquet[Keys[x][[#]] &, u, X])^2], trainset];

  sse = totalSquareResidual / ( Length@trainset - Length@X - 1);

  (*必要なパラメータだけで再番号付け*)
  posAssc =
      Association@
          MapIndexed[toSubsetNumber[#1, X] -> First@#2 &,
            coveringParameters@covering];

  M = toMobiusMatrix[Keys@trainset, X, covering];
  shrinkedM = Map[
    Function[x, KeyValueMap[x[[#1]] &, posAssc]]
    ,
    M
  ];
  MM = Quiet@Inverse[Transpose[shrinkedM] . shrinkedM];

  If[Head@MM==Inverse,
    MM = PseudoInverse@First@MM;
  ];

  posAssc2 =
      Association@MapIndexed[#1 -> First@#2 &, coveringParameters@covering];

  tvalues = AssociationMap[
    Function[A,
      i = posAssc2[A];
      mobiusParams[A] / Sqrt[MM[[i, i]] * sse]
    ]
    ,
    coveringParameters@covering
  ];






  Return@<|
    "measure" -> params,
    "covering" -> covering,
    "parameterNum" -> Length@heredityFamily@covering - 1,
    "totalSquareResidual" -> totalSquareResidual,
    "AIC" -> Length@trainset * Log[totalSquareResidual / Length@trainset] + 2 * (Length@heredityFamily@covering - 1),
    "BIC" -> Length@trainset * Log[totalSquareResidual / Length@trainset] + (Length@heredityFamily@covering - 1) * Log[Length@trainset],
    "t-values" -> tvalues
  |>
]

(*
包除族は，sortとmaxされてると仮定する．
trainsetの型は"1"種類のみ：
{{0, 0, 0, 0, 0, 0} -> 0, {0, 0, 0, 0, 0, 1/2} -> 0...}
<|obj -> {x1,x2} -> label,...|>
評価基準集合は数字番号とする．
*)





(*
引数に取るXの集合族はWolfram関数のSort順（要素数が小さい順、要素数が同じものは辞書式順序）とする。
*)

fromFocus[m_,A_List,focuses_List] := Total@Map[m, Select[MemberQ[focuses, #] &]@Subsets[A, {1, Length@A}]]




toFullAssociation[u_, X_List] := AssociationMap[If[MissingQ@u[#], 0, u[#]] &, Subsets[X]]


toSubsetVector[poly_, u_, X_List] :=
    Normal@SparseArray[#, {2^Length@X - 1}] &@
        Map[toSubsetNumber[First[#], X] -> Coefficient[poly, #] &,
          Select[Head@# == u &]@Variables[poly]]


(*DEF:ショケ積分回帰モデルにおいて、
X上の集合関数trueMeasure、
誤差項を平均０、標準偏差eの正規乱数、
被積分関数を区間[0,1]上の一様乱数としたn組の訓練データを生成する*)
createTrainset[sampleNumber_Integer, num_Integer,error_] := createTrainset[coveringFuzzyExamples[sampleNumber]["u"],coveringFuzzyExamples[sampleNumber]["X"], num,error]
createTrainset[trueMeasure_, X_List,  n_Integer,e_] := Module[{u},
  Function[x,
    x -> ReplaceAll[
      choquet[x[[#]] &, u, X] +
          RandomVariate@NormalDistribution[0, e],
      Map[u[#] -> trueMeasure[#] &]@Subsets[X]]
  ] /@ Array[RandomReal[] &, {n, Length@X}]
]

experimentDirectory[ex_Integer, num_Integer, sd_] := FileNameJoin@{$fuzzyProjectPath, "experiments", "ex=" <> ToString@ex,"num=" <> ToString@num, "sd=" <> ToString@sd}
experimentDirectory[ex_Integer, num_Integer] := FileNameJoin@{$fuzzyProjectPath, "experiments", "ex=" <> ToString@ex,"num=" <> ToString@num}
experimentDirectory[ex_Integer] := FileNameJoin@{$fuzzyProjectPath, "experiments", "ex=" <> ToString@ex}

$dataNums = {10, 25, 50, 100, 200, 400, 800}
$sds = {0.01, 0.1, 1.0}




(*訓練データ生成１
$dataNums = {10, 25, 50, 100, 200, 400, 800}
$sds = {0.01, 0.1, 1.0}

Function[ex,
  Do[PrintTemporary[{dataNum, sd}];
   saveTrainsets[ex, dataNum, sd, 3,
    True], {dataNum, $dataNums}, {sd, $sds}]] /@
 Range@Last@Keys@coveringFuzzyExamples
*)

saveTrainsets[exampleNumber_Integer, dataNum_Integer, sd_?NumberQ,trainsetNum_Integer,overWriteQ_?BooleanQ,rootDir_String:Missing[]] := Module[
  {
    dir,
    path
  },
  If[MissingQ@coveringFuzzyExamples[exampleNumber], Echo@"not exist";
  Return@$Failed];
  If[MissingQ@rootDir,
    dir = experimentDirectory[exampleNumber, dataNum, sd],
    dir = rootDir
  ];

  dir = FileNameJoin@{dir,"trainsets"};

  If[Not@FileExistsQ@dir, CreateDirectory@dir];
  Function[i,
    path = FileNameJoin@{dir, ToString@i <> ".wxf"};
    If[Not@FileExistsQ@path || FileExistsQ@path && TrueQ@overWriteQ,
      Export[path, createTrainset[exampleNumber, dataNum, sd]];
      ,
      EchoLabel["error:"]@path;
      Return@$Failed;
    ]
  ] /@ Range@trainsetNum;
  Return@dir;
]

(*
saveKnownAlgorithm/@SortBy[ToExpression@First@First@StringPosition[#,"="]&]@FileNames["*","C:\\Users\\MT4ver2-h23-EgpgNqbS\\Desktop\\experiments",{1}]

*)
$knownAlgorithmName = "known algorithm"
$newAlgorithm1 = "inequality 3"


saveKnownAlgorithm[rootDir_String] := saveAlgorithm[rootDir,$knownAlgorithmName]

findOptimalModelBy[algoName_String,trainset_]:=Switch[algoName,
  $knownAlgorithmName,findOptimalModelByCSA1[trainset],
  $newAlgorithm1, findOptimalModelByCSA2[trainset,("inequality"-> 3)] ,
  _,Abort[]
]

saveAlgorithm[rootDir_String, algoName_String] := Module[{i=0,currentPath},
  PrintTemporary[Column@{Dynamic@i,Dynamic@currentPath}];
  Function[path,
    currentPath = path;
    Module[{res, dir,newPath},
      i++;
      dir = FileNameJoin@{ParentDirectory@DirectoryName@path,algoName};
      If[Not@FileExistsQ@dir, CreateDirectory@dir];
      newPath =FileNameJoin@{dir, FileNameTake@path};
      If[Not@FileExistsQ@newPath,
        res = findOptimalModelBy[algoName,Import@path];
        Export[newPath, res];
      ];
    ]
  ] /@ EchoFunction[Length]@Flatten@Map[FileNames["*.wxf", #, Infinity] &]@FileNames["trainsets", rootDir, Infinity]

]


calcAllCoverings[X_List] := Module[{params, memoQ,calcBiggers},
  params = Subsets[X, {1, Length@X}];
  (*DEF:gを含む包除被覆を全て求める*)
  calcBiggers[g_] := Module[{xs, new},
    xs = minimalFamily@Complement[params, coveringParameters@g];
    Flatten[#, 1] &@Map[
      Function[x,
        new = maximalFamily@Sort@Append[g, x];
        If[TrueQ@memoQ[new],
          Nothing
          ,
          memoQ[new] = True;
          Sow@new;
          calcBiggers[new]
        ]
      ]
      , xs]
  ];
  First@Last@Reap@calcBiggers[Sow@Subsets[X, {1}]]
]


(*アルゴリズムフォルダ => シンプルな指標Assc*)
(*<|"jaccard" -> <|"mean" -> 0.966667, "sd" -> 0.105409|>, "dice" -> <|"mean" -> 0.466715, "sd" -> 0.314331|>|>*)
createOptDistanceTable[rootExFolder_,nums_List,sds_List,algoName_String]:=Module[{assc},
  assc=createOptDistanceAsscEx[rootExFolder,nums,sds,algoName];
  TableForm[
    Table[
      If[MissingQ@#,#,
      Row@{
      Round[#["jaccard"]["mean"],0.01],"\[PlusMinus]",Round[#["jaccard"]["sd"],0.01]
    }]&@assc[n,s],{n,nums},{s,sds}]
    ,
    TableHeadings->{nums,sds}
  ]
]

createOptDistanceAsscEx[rootExFolder_,nums_List,sds_List,algoName_String]:=
    AssociationMap[
      Function[num,
        createOptDistanceAsscNum[FileNameJoin@{rootExFolder,"num="<>ToString@num},sds,algoName]
      ]
      ,
      nums
    ]

createOptDistanceAsscNum[rootNumFolder_,sds_List,algoName_String]:=
    AssociationMap[
      Function[sd,createOptDistanceAsscCV@FileNameJoin@{rootNumFolder,"sd="<>ToString@sd,algoName}
      ]
      ,
      sds
    ]

(*アルゴリズムフォルダ => シンプルな指標Assc*)
createOptDistanceAsscCV[rootCVFolder_String]:=
    Module[{xs,ex},
      ex=ToExpression@StringDelete["ex="]@FileNameTake@ParentDirectory[rootCVFolder,3];
      xs=Map[
        Function[resultObject,
          If[AssociationQ@resultObject,
            Module[{},
              <|
                "coveringSimilarity" -> N@coveringSimilarity[coveringFuzzyExamples[ex]["covering"], resultObject["optCovering"],coveringFuzzyExamples[ex]["X"]],
                "measureDistance" -> N@measureDistance[coveringFuzzyExamples[ex]["u"],resultObject["models"][resultObject["optCovering"]]["measure"],coveringFuzzyExamples[ex]["X"]],
                "searchLength" -> Length@resultObject["calcedCoverings"]
              |>
            ]
            ,
(*            Echo@"Missing resultObject"<>ToString@ex;*)
            Missing["T-Dist"]
          ]
        ]@*Import
      ]@FileNames["*.wxf",rootCVFolder];
      xs = DeleteMissing@xs;
      If[Length@xs==0,
        Missing["T-Dist"]
        ,
        AssociationMap[
          Function[key,<|"mean"->Mean@#,"sd"->StandardDeviation@#|>&@Map[#[key]&]@xs],
          {"coveringSimilarity","measureDistance","searchLength"}
        ]
      ]
    ]


(*
expaths=SortBy[ToExpression@StringTake[#,1+First@First@StringPosition[#,"="];;]&]@FileNames["*","C:\\Users\\MT4ver2-h23-EgpgNqbS\\Desktop\\experiments",{1}];
*)

experimentCounter[exPath_] := Module[
  {
    xs
  },
  xs = Flatten[#, 1] &@createResultMatrix@exPath;
  Map[Total]@
      Transpose@
          Select[NumberQ@Total@# &]@
              Map[Function[
                x, {Boole[x[[1, 3]] < x[[2, 3]]], Boole[x[[1, 3]] > x[[2, 3]]],
                  Boole[x[[1, 3]] > x[[2, 3]] && x[[1, 1]] < x[[2, 1]] &&
                      x[[1, 2]] >= x[[2, 2]] ||
                      x[[1, 1]] <= x[[2, 1]] && x[[1, 2]] > x[[2, 2]]],
                  Boole[x[[1, 3]] > x[[2, 3]] && x[[1, 1]] > x[[2, 1]] &&
                      x[[1, 2]] <= x[[2, 2]] ||
                      x[[1, 1]] >= x[[2, 1]] && x[[1, 2]] < x[[2, 2]]]}], xs
              ]
]

createResultMatrix[rootExFolder_String] :=Module[
  {
    CSA2, CSA1,
    fuzzyDistance1,fuzzyDistance2
    ,coveringSimilarity1,coveringSimilarity2
    ,searchLen1,searchLen2,
    misser
  },
  CSA2 = createOptDistanceAsscEx[rootExFolder, $dataNums, $sds, $newAlgorithm1];
  CSA1 = createOptDistanceAsscEx[rootExFolder, $dataNums, $sds, $knownAlgorithmName];

  Table[
    misser = If[Not@NumberQ@#, "NaN", Round[N@#, 0.01]]&;

    fuzzyDistance1 = misser@Round[CSA1[n, s]["measureDistance"]["mean"], 0.01];
    fuzzyDistance2 = misser@Round[CSA2[n, s]["measureDistance"]["mean"], 0.01];

    coveringSimilarity1 = misser@Round[CSA1[n, s]["coveringSimilarity"]["mean"], 0.01];
    coveringSimilarity2 = misser@Round[CSA2[n, s]["coveringSimilarity"]["mean"], 0.01];

    searchLen1 = misser@CSA1[n, s]["searchLength"]["mean"];
    searchLen2 = misser@CSA2[n, s]["searchLength"]["mean"];

    Transpose@{
      {
        fuzzyDistance1,
        fuzzyDistance2
      },
      {
        coveringSimilarity1,
        coveringSimilarity2
      },
      {
        searchLen1,
        searchLen2
      }
    }

    , {n, $dataNums}, {s, Reverse@$sds}
  ]
]

createResultTable[rootFolder_String]:=Module[
  {
    xs,
    $ronbunTabler2,
    innerGrider
  },
  $ronbunTabler2 = Function[rootExFolder,
    Module[
      {
        CSA2, CSA1,
        fuzzyDistance1,fuzzyDistance2
        ,coveringSimilarity1,coveringSimilarity2
        ,searchLen1,searchLen2,
        misser
      },
      CSA2 = createOptDistanceAsscEx[rootExFolder, $dataNums, $sds, $newAlgorithm1];
      CSA1 = createOptDistanceAsscEx[rootExFolder, $dataNums, $sds, $knownAlgorithmName];
      (*    TableForm[#, TableHeadings -> {$dataNums, Reverse@$sds}] &@*)
      Table[
        misser = If[Not@NumberQ@#, "NaN", Round[N@#, 0.01]]&;

        fuzzyDistance1 = misser@Round[CSA1[n, s]["measureDistance"]["mean"], 0.01];
        fuzzyDistance2 = misser@Round[CSA2[n, s]["measureDistance"]["mean"], 0.01];

        coveringSimilarity1 = misser@Round[CSA1[n, s]["coveringSimilarity"]["mean"], 0.01];
        coveringSimilarity2 = misser@Round[CSA2[n, s]["coveringSimilarity"]["mean"], 0.01];

        searchLen1 = misser@CSA1[n, s]["searchLength"]["mean"];
        searchLen2 = misser@CSA2[n, s]["searchLength"]["mean"];

        Transpose@{
          {
            Style[fuzzyDistance1, If[fuzzyDistance1 < fuzzyDistance2, Blue, Black]],
            Style[fuzzyDistance2, If[fuzzyDistance1 > fuzzyDistance2, Green, Black]]
          },
          {
            Style[coveringSimilarity1, If[coveringSimilarity1 > coveringSimilarity2, Blue, Black]],
            Style[coveringSimilarity2, If[coveringSimilarity1 < coveringSimilarity2, Green, Black]]
          },
          {
            Style[searchLen1, If[searchLen1 < searchLen2, Blue, Black]],
            Style[searchLen2, If[searchLen1 > searchLen2, Green, Black]]
          }
        }

        , {n, $dataNums}, {s, Reverse@$sds}
      ]
    ]
  ];


  xs=$ronbunTabler2@rootFolder;
  innerGrider=If[AnyTrue[Flatten@#,First@#==="NaN"&],"-",Grid[#,
    Dividers->{{2->LightGray,3->LightGray},{2->LightGray}},ItemSize->{4*{1,1,1}},Spacings->{0.1,0.2},Alignment->{Center,Center}]]&;
  Grid[Prepend[Prepend[""]@$dataNums]@Transpose@Prepend[Reverse@$sds]@Map[Map[innerGrider]]@xs,Dividers->{{1->Black,2->Gray,Apply[Sequence]@Map[#->Gray&,{3,4,5,6,7,8}],9->Black},{1->Black,2->Gray,Apply[Sequence]@Map[#->Gray&,{3,4}],5->Black}},Spacings->{0.1,0.1},Alignment->{Center,Center}]
]


(*
trainsetから求まるメビウス計画行列と応答ベクトルで線形回帰を計算する.
包除被覆coveringを引数にとった場合，
*)
mobiusLinearModel[trainset_List,covering_List:Missing[]]:= Module[{resultObject = <||>},
  (
    resultObject["timing"] = #["Timing"];
    resultObject["absoluteTiming"] = #["AbsoluteTiming"];
  ) &@EvaluationData@Module[
    {
      X = Range@Length@Keys@First@trainset,
      mobiusMatrix,
      mobiusLM,
      quantile,
      tValues
    },


    mobiusMatrix = toMobiusMatrix[Keys@trainset,X,covering];


    mobiusLM = LinearModelFit[{mobiusMatrix, Values@trainset}];
    resultObject["mobiusLinearModel"] = mobiusLM;

    resultObject["mobiusMatrix"] = Iconize@mobiusMatrix;

    tValues = KeySelect[MissingQ@covering || MemberQ[coveringParameters@covering, #] &]@KeySort@Quiet@AssociationThread[fromSubsetNumber[#, X] & /@ Range[2^Length@X - 1] -> mobiusLM["ParameterTStatistics"]];
    resultObject["tValues"] = tValues;

    resultObject["bestFitParameters"] = KeySort@Quiet@AssociationThread[fromSubsetNumber[#, X] & /@ Range[2^Length@X - 1] -> mobiusLM["BestFitParameters"]];

    resultObject
  ];
  Return@resultObject
]