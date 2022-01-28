

parents[g_List,X_List] := Select[Subsets[X,{2,Length@X}],Function[x,Not@MemberQ[g,x]&&SubsetQ[g,Subsets[x,{Length@x-1}]]]]

findOptimalModelByCSA2[trainset_List,stopper_Rule:("inequality"-> 3),monitorQ_:False]:= Module[
  {
    calcedCoverings = {},
    X = Range@Length@Keys@First@trainset,
    criteria,
    minIC = <||>,
    model = <||>,
    calcModel,
    mobiusLM,
    mobiusCovering,
    criteriaOrder,
    gs,
    hmax,
    coverings,
    resultObject = <||>,
    criteriaValue,
    quantile,
    tValues,
    endQ = False,
    calcResultObject,
    tValues2,
    minICmodels,
    nexts,
    calcTValue
  },

  If[Length@trainset - 2^Length@X - 1 <= 0,
    Return@"Error:StudentTDistribution:データ数が足りない";
  ];

  If[monitorQ,
    PrintTemporary[Dynamic@Column@MapIndexed[Row@{First@#2, " : ", #1} &]@calcedCoverings]
  ];

  (*DEF:*)
  nexts[g_List]:=Module[{A,ps,ms,xs,newCovering},

    ps=parents[g,X];
(*    MinimalBy[#, Length] &@*)
    ms=minimalFamily@Complement[Subsets[X, {1, Length@X}], coveringParameters@g];

    xs = DeleteDuplicates[ps~Join~ms];
    newCovering = Sort@maximalFamily@Join[g,xs];
    If[monitorQ,
      EchoLabel["ms"]@ms;
      EchoLabel["parents"]@ps;
      EchoLabel["xs"]@xs;
      EchoLabel["newCovering"]@newCovering;
    ];
    If[Length@xs==1,
      Return[xs];
      ,
      A=Last@SortBy[Abs@calcTValue[newCovering,#] &]@xs;
      Return[{A}];
    ];
  ];

  (*DEF:*)
  calcTValue[covering_List,A_List]:=Module[
    {

    },
    If[Not@MemberQ[calcedCoverings,covering],
      calcModel[covering];
    ];
    Return@model[covering]["t-values"][A]
  ];

  (*DEF:包除被覆coveringでのモデルを計算する*)
  calcModel[covering_List] := With[
    {n = Length@coveringParameters@covering},
    If[MemberQ[calcedCoverings,covering],Return[]];
    model[covering] = coveringFuzzyRegression[trainset,covering];
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
    ];
    Return@resultObject;
  ];


  (*線形モデルの同定*)
  calcModel[Subsets[X, {1}]];
  mobiusLM = mobiusLinearModel[trainset,Subsets[X, {2}]];
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
  tValues2 = model[Subsets[X, {2}]]["t-values"];
  resultObject["tValues2"] = tValues2;



  quantile = Quantile[StudentTDistribution[Length@trainset - 2^Length@X - 1], 0.975];
  resultObject["quantile"] = quantile;

  tValues=KeySort@Quiet@AssociationThread[fromSubsetNumber[#, X] & /@ Range[2^Length@X - 1] -> mobiusLM["mobiusLinearModel"]["ParameterTStatistics"]];
  resultObject["tValues"] = tValues;

  If[Length@X == 2,
    Return@calcResultObject[];
  ];

  mobiusCovering = Keys@Select[Abs@# > quantile&]@KeySelect[Length@# == 2 &]@tValues2;
  mobiusCovering = Sort[mobiusCovering~Join~Map[List]@Complement[X, Union @@ mobiusCovering]];

  If[mobiusCovering != {},
    calcModel[mobiusCovering];
  ];
  resultObject["mobiusCovering"] = mobiusCovering;

  If[Length@mobiusCovering==0,
    gs = {Subsets[X,{1}]},
    gs = {mobiusCovering};
  ];

  While[True,

    If[monitorQ,
      Pause[1];
      If[monitorQ,EchoLabel["gs"],Identity]@gs;
      (*      Echo@Column@calcedCoverings;*)
    ];

    coverings = First@Last@Reap@Map[
      Function[g,
        Function[A,
          Module[{covering},
            covering = maximalFamily@Sort@Append[A]@g;
            calcModel[Sow@covering];
            If[covering == {X}, endQ = True];
          ]
        ] /@ If[monitorQ,EchoLabel["nexts"],Identity]@nexts[g]
      ],
      gs
    ];

    If[monitorQ,EchoLabel["coverings"],Identity]@coverings;
    gs = minICmodels[coverings];

    hmax = Max@Keys@minIC;
    If[endQ ||
 (*       Switch[Keys@stopper,
          "inequality", Apply[LessEqual]@Map[minIC[hmax - #] &, Reverse@Range@Values@stopper] <= minIC[hmax],
          "minimum", TrueQ[AllTrue[hmax-Reverse@Range[0,Values@stopper-1],minIC[hmax-Values@stopper]<=minIC[#]&]],
          True, Echo@"unavailable stoppertype"
        ]*)
        AnyTrue[Quiet@Range[Length@X+3,hmax],TrueQ[minIC[# - 3] <= minIC[# - 2] <= minIC[# - 1] <= minIC[#]]&]
(*      False*)
      ,
      Return@calcResultObject[];
    ];


  ];

]
