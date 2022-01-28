
(*DEF:変数増減法により準最適なモデルを探索した結果を返す

結果は連想型で返される。
"linearModel" : 線形モデルの同定結果オブジェクト
"criteriaValue" : 使用する情報量基準の選択で使う評価値
"criteria" : 使用する情報量基準
"mobiusLinearModel" : 仮説検定で用いるメビウス変換の線形モデルの同定結果オブジェクト
"tValues" : 仮説検定で各パラメータのT値の連想
"quantile" : 仮説検定の棄却水準
"optCoverings" : 準最適な包除被覆の集合
"minIC" : 終了条件までのモデル群の中で、最小の情報量
*)

findOptimalModelByCSA1[trainset_List,monitorQ_:False]:= Module[
  {
    calcedCoverings = {},
    threeCoverings = {},
    X = Range@Length@Keys@First@trainset,
    criteria,
    minIC = <||>,
    model = <||>,
    calcModel,
    mobiusLM,
    mobiusCovering,
    criteriaOrder,
    gs,
    hs,
    ts,
    hmax,
    coverings,
    minimals,
    u,
    resultObject = <||>,
    quantile,
    tValues,
    calcResultObject,
    gsPrev,
    minICmodels
  },

  If[monitorQ,
    PrintTemporary[Dynamic@Column@MapIndexed[Row@{First@#2, " : ", #1} &]@calcedCoverings]
  ];

  (*包除被覆coveringのモデルを計算し，minICを更新する*)
  calcModel[covering_List] := With[
    {
      n = Length@coveringParameters@covering
    },
    If[MemberQ[calcedCoverings, covering], Return[]];
    model[covering] = coveringFuzzyRegression[trainset, covering];
    AppendTo[calcedCoverings, covering];
    minIC[n] = If[NumberQ@minIC[n], Min[minIC[n], model[covering][criteria]], model[covering][criteria]]
  ];

  criteriaOrder[A_, B_] :=
      Which[
        model[A][criteria] <= model[B][criteria] - 2, 1,
        model[B][criteria] <= model[A][criteria] - 2, -1,
        True, 0
      ];

  (*coveringsで最適なモデル集合を得る*)
  minICmodels[covs_] :=
      With[{min = Min[model[#][criteria]& /@ covs]},
        Return@Select[covs, model[#][criteria] - min < 2&]
      ];

  calcResultObject[] := Module[{},
    With[{min = Min[model[#][criteria] & /@ calcedCoverings]},
      resultObject["minICs"] = minIC;
      resultObject["calcedCoverings"] = calcedCoverings;
      resultObject["models"] = model;
      resultObject["optCoverings"] = Select[calcedCoverings, model[#][criteria] - min < 2 &];
      resultObject["optCovering"] = SelectFirst[calcedCoverings, model[#][criteria] == min &];
      resultObject["minIC"] = min;
      (*        resultObject["criteria plot"] = ListLinePlot@Map[resultObject["models"][#][resultObject["criteria"]] &, resultObject["calcedCoverings"]];*)
      (*        Print@Style[resultObject["optCoverings"],Green];*)(*TODO:*)
    ];
    Return@resultObject;
  ];


  (*線形モデルの同定*)
  calcModel[Subsets[X, {1}]];


  (*t-Valeus実験のため単調性なしも求めておく*)
  mobiusLM = mobiusLinearModel[trainset, Subsets[X, {2}]];
  resultObject["mobiusLinearModel"] = mobiusLM;


  (*使用する情報量基準の選択*)
  Module[{criteriaValue},
    criteriaValue = model[Subsets[X, {1}]]["totalSquareResidual"] / Total[Values[trainset]^2];
    criteria = If[criteriaValue <= 0.05, "BIC", "AIC"];
    resultObject["criteria"] = criteria;
    resultObject["criteriaValue"] = criteriaValue;
    minIC[Length@X] = model[Subsets[X, {1}]][criteria];
  ];

  (*２要素集合のモデル同定*)
  calcModel[Subsets[X, {2}]];

  If[Length@trainset - 2^Length@X - 1 <= 0,
    Return@"Error:StudentTDistribution:データ数が足りない";
  ];

  quantile = Quantile[StudentTDistribution[Length@trainset - 2^Length@X - 1], 0.975];
  resultObject["quantile"] = quantile;

  tValues = model[Subsets[X, {2}]]["t-values"];
  resultObject["tValues"] = tValues;

  mobiusCovering = Keys@Select[Abs@# > quantile&]@KeySelect[Length@# == 2 &]@tValues;
  mobiusCovering = Sort[mobiusCovering~Join~Map[List]@Complement[X, Union @@ mobiusCovering]];

  If[mobiusCovering != {},
    calcModel[mobiusCovering];
  ];
  resultObject["mobiusCovering"] = mobiusCovering;


  (*選定された3要素集合*)
  Map[
    Function[A,
      With[{covering = Sort@maximalFamily@Append[mobiusCovering, A]},
        calcModel[covering];
        If[criteriaOrder[covering, mobiusCovering] == 1, AppendTo[threeCoverings, covering]];
      ]
    ],
    Subsets[X, {3}]
  ];

  (*線形モデルが最適か判定*)
  If[AllTrue[{Subsets[X, {2}], mobiusCovering} ~ Join ~ threeCoverings, criteriaOrder[Subsets[X, {1}], #] === 1&],
    Return@calcResultObject[];
  ];


  If[Length@X == 2,
    Return@calcResultObject[];
  ];



  If[Length@threeCoverings === 0,
    If[Length@mobiusCovering==0,
      gs = {Subsets[X,{1}]},
      gs = {mobiusCovering};
    ];
    hs = {};
    ,
    (*threeCoveringsでパラメータ数が最小なものとそうでないものを分ける*)
    gs = MinimalBy[threeCoverings, Length@coveringParameters@#&];
    hs = Complement[threeCoverings, gs];
  ];

  While[True,

    If[monitorQ,
      Pause[1];
      Echo@gs;
(*      Echo@Column@calcedCoverings;*)
    ];


    If[Length@gs === 1,
      With[{g = First@gs},
        minimals = minimalFamily@Complement[Subsets[X, {1, Length@X}], coveringParameters@g];
        coverings = Map[Sort@maximalFamily@Append[g, #]&, minimals];
        ts = Select[Length@coveringParameters@g + 1 === Length@coveringParameters@#&]@hs;
      ];
      calcModel /@ coverings;
      ,
      coverings = Map[Sort@maximalFamily[Union @@ #]&, Subsets[gs, {2}]];

      ts = Select[Length@coveringParameters@First@gs + 1 === Length@coveringParameters@#&]@hs;
      calcModel /@ coverings;
    ];

    gsPrev = gs;
    gs = DeleteDuplicates@minICmodels[coverings ~ Join ~ ts];

    (*終了条件*)
    hmax = Max@Keys@minIC;
    If[AnyTrue[Quiet@Range[Length@X+3,hmax],TrueQ[minIC[# - 3] <= minIC[# - 2] <= minIC[# - 1] <= minIC[#]]&]
        || If[Last@calcedCoverings === {X},Echo[Column@{gsPrev,gs}];True,False] || If[Length@gs ==0,Echo[Column@{gsPrev,gs}];True,False] || If[gsPrev === gs,Echo[Column@{gsPrev,gs}];True,False],
      Return@calcResultObject[];
    ];
  ];
]