

(*DEF:全ての直和分割を求める*)
(*包除被覆の数を求める関数を作ろうとしたら直和分割になってた（笑）*)
calcPartitions[X_List]:=Module[{
  h,
  g,
  memo,
  coveringToCoverings,
  coveringToCoveringsRecursive
},
  h = Function[{xs, i},
    {xs[[;; i]], xs[[i + 1 ;;]]}
  ];
  g = Function[xs, Map[h[xs, #] &, Range[Length@xs - 1]]];

  (*coveringより真に大きい *)
  coveringToCoverings[covering_] := (
    Flatten[#, 1] &@Map[
      Function[A,
        Map[Union[DeleteCases[covering, A, 1], #] &, g@A]
      ], Select[Length@# >= 2 &]@covering
    ]
  );

  coveringToCoveringsRecursive[cov_] :=
      Function[covering,
        If[TrueQ[memo[covering]],
          Nothing,
          memo[covering] = True;
        Sow[covering];
          coveringToCoveringsRecursive[covering]
        ]
      ] /@ coveringToCoverings[cov];

  Return@Last@Last@Reap@coveringToCoveringsRecursive@{Sow@X}
]