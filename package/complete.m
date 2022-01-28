

maximalFamily[S_List] :=Select[S,Function[x,Not@*Or @@ Map[SubsetQ[#, x] &, DeleteCases[S, x,1]]]]

minimalFamily[S_List] :=Select[S,Function[x,Not@*Or @@ Map[SubsetQ[ x,#] &, DeleteCases[S, x,1]]]]

heredityFamily[S_List] := Union@Flatten[Subsets /@ S, 1]


monotoneConditions[u_,X_List]:=Flatten@Table[Map[Function[xs,(u[xs]>=If[#=={},0,u[#]])&/@Subsets[xs,{Length@xs-1}]]]@Subsets[X,{i}],{i,1,Length@X}]

toMobius[u_, A_List] := Total@Map[(-1)^Length@Complement[A, #]*u[#] &, Subsets[A,{1,Length@A}]]

fromMobius[m_,A_List] := Total@Map[m, Subsets[A,{1,Length@A}]]

toMobiusMeasure[u_,X_List] :=  AssociationMap[toMobius[u, #] &, Subsets[X]]

fromMobiusMeasure[m_,X_List] := AssociationMap[fromMobius[m, #] &, Subsets[X]]

measureDistance[u1_, u2_, X_List] :=
    Total@Map[Abs[u1[#] - u2[#]]^2 &]@Subsets[X]

shapleyValue[x_, u_, X_List] := Total@Map[
  1/(Length@X*Binomial[Length@X - 1, Length@#])*(u@Union[#, {x}] - u@#) &
  , Subsets@DeleteCases[X, x]]

interactionIndex[x1_, x2_, u_, X_] := Total@Map[
  1/((Length@X - 1)*
      Binomial[Length@X - 2, Length@#])*(u@Union[#, {x1, x2}] -
      u@Union[#, {x1}] - u@Union[#, {x2}] + u@#) &
  , Subsets@DeleteCases[X, x1 | x2]]

interactionIndexFromMobius[x1_,x2_,m_,X_List]:=Total@Map[
  1/(Length@#+1)*m@Union[#,{x1,x2}]&
  ,Subsets@DeleteCases[X,x1|x2]]

monotoneQ[u_,X_]:=And @@ monotoneConditions[u, X]

monotoneMobiusConditions[m_,X_List]:=Flatten@Map[
  Function[c,
    Map[
      Function[A,
        Total@Map[Function[B,m[Union[B,{c}]]],DeleteCases[c]@Subsets[A]]>=0
      ]
      ,
      Select[Not@MemberQ[#,c]&]@Subsets[X]
    ]
  ],
  X
]

toSubsetNumber[A_List, X_List] := toSubsetNumber[A,X] =
    FromDigits[SparseArray[Map[# -> 1 &, A], {Length@X}], 2]

fromSubsetNumber[n_Integer, X_List] := fromSubsetNumber[n,X] =
    Pick[X, PadLeft[IntegerDigits[n, 2], Length@X], 1]

choquet[f_,u_,X_List]:=Map[u@*Sort]@NestList[Most,ReverseSortBy[X,f],Length@X-1].
    Prepend[Differences@#, First@#]&@Sort[f/@X]

choquetFromMobius[f_,m_,X_List]:=Total@Map[Min[f/@#]*m@#&,Subsets[X,{1,Length@X}]]

coveringParameters[covering_]:=Rest@heredityFamily@covering

coveringSimilarity[covering1_, covering2_,X_] := Module[{h1, h2,f1,f2},
  h1 = heredityFamily@covering1;
  h2 = heredityFamily@covering2;
  f1=Length@Intersection[h1, h2]-Length@X-1;
  f2=Length@Union[h1, h2]-Length@X-1;
  If[f1==f2==0,1,(f1)/(f2)]
]


fromCovering[u_, S_List, A_] := Function[K,
  (-1)^(Length@K + 1)*If[#===u[{}],0,#]&@u[Intersection[Sequence @@ K, A]]
] /@ Subsets[S, {1, Length@S}] // Total

fromCoveringMobius[m_, S_List, A_List] :=
    Module[{u}, fromCovering[u, S, A] /. u[B_] :> fromMobius[m, B]
    ]