(* ::Package:: *)

(* ::Section:: *)
(*The functions handling the evolution of programs*)


BeginPackage["ProgramEvolution`"]


(* ::Section:: *)
(*BNF grammar rules*)


rulesP = {root -> Inactivate[listfunction[list, crit]],
		listfunction -> Inactivate[Select],
		list :> Inactivate[Table[RandomInteger[10], RandomInteger[10]]],
		list :> Inactivate[Table[expr, {z, 0, RandomInteger[{1, 10}]}]],
		expr :> Inactivate[z],
		expr :> Inactivate[const],
		expr :> expr+expr,
		expr :> expr-expr,
		expr :> expr*expr,
		expr :> expr/expr,
		const :> RandomReal[10],
		crit :> Inactivate[(puref > RandomInteger[1] &)],
		crit :> Inactivate[(puref < RandomInteger[20] &)],
		puref :> Inactivate[#],
		puref :> Inactivate[const],
		puref :> puref+puref,
		puref :> puref-puref,
		puref :> puref*puref,
		puref :> puref/puref};


(* ::Section:: *)
(*Random derivation tree*)


RandomDerivation[expr_, rules_, previ_, g_] :=
	Module[
		{keyList, list, index, new, node, gr},
		keyList = Keys[Counts[Keys[rules]]];
		If[Length[Select[keyList, Length[Position[expr, #]] != 0 &]] == 0, Return[g]];
		gr = g;
		keyList = Keys[Counts[Keys[rules]]];
		Map[
			With[
				{key = #},
				Map[
					With[
						{pos = #},
						list = Select[rules, #[[1]] == key &];
						index = RandomInteger[{1, Length[list]}];
						new = Last[list[[index]]];
						node = {key, index, RandomInteger[100000]};
						gr = EdgeAdd[gr, previ -> node];
						gr = RandomDerivation[new, rules, node, gr]
					]&,
					Position[expr, key]
				]
			]&,
			keyList
		];
		gr
	];


(* ::Section:: *)
(*Create program from derivation tree*)


CodeFromDerivation[derivGraph_, rules_] :=
	Module[
		{expr, expr2, keyList, pos, currentNodes2},
		expr = First[First[Select[VertexList[derivGraph], VertexInDegree[derivGraph, #] == 0 &]]];
		expr2 = expr;
		keyList = Keys[Counts[Keys[rules]]];
		NestWhile[
			With[
				{currentNodes = #},
				currentNodes2 = Flatten[Map[
					With[
						{node = #},
						Select[node /. #& /@ EdgeRules[derivGraph], ToString[#] != ToString[node]&]
					]&,
					currentNodes
				], 1];
				expr2 = expr;

				Map[
					With[
						{key = #},
						pos = Position[expr, key];
						keyNodes = Select[currentNodes, #[[1]] == key &];
						keyMappings = #[[2]] & /@ Select[rules, #[[1]] == key &];
						If[
							ToString[expr] == ToString[key],
							expr2 = Replace[expr2, key -> keyMappings[[keyNodes[[1]][[2]]]]],
							For[i = 1, i <= Length[pos], ++i, keyMappings = #[[2]] & /@ Select[rules, #[[1]] == key &]; expr2 = ReplacePart[expr2, pos[[i]] -> keyMappings[[keyNodes[[i]][[2]]]]]];
						];
					]&,
					keyList
				];
				expr = expr2;
				currentNodes2
			]&,
			Select[VertexList[derivGraph], VertexInDegree[derivGraph, #] == 0 &],
			With[
				{nodes = #},
				Length[nodes] > 0
			]&
		];
		expr
	];


(* ::Section:: *)
(*Replace subgraph utility function*)


ReplaceDerivationSubgraph[originalG_, newBranch_, originNode_] :=
	Module[
		{newG, deleteVertices},
		parent = First[Select[EdgeList[originalG], #[[2]] == originNode &]][[1]];
		newOrig = First[Select[VertexList[newBranch], VertexInDegree[newBranch, #] == 0 &]];
		newG = EdgeAdd[originalG, Join[EdgeList[newBranch], {parent -> newOrig}]];
		deleteVertices = 
			Flatten[NestWhileList[
				With[
					{currentNodes = #},
					Flatten[
						Map[
							With[
								{node = #},
								Select[node /. #& /@ EdgeRules[newG], ToString[#] != ToString[node]&]
							]&,
							currentNodes
						], 
						1
					]
				]&,
				{originNode},
				Length[#] > 0 &
			],1];
		deleteVertices = DeleteDuplicates[deleteVertices];
		newG = VertexDelete[newG, deleteVertices];
		newG
	];


(* ::Section:: *)
(*Derivation graph mutation*)


DerivationGraphMutation[rules_][graphD_] :=
	Module[
		{element, parent, newDeriv, newElement, deleteVertices},
		element = RandomChoice[VertexList[graphD]];
		If[Length[Select[EdgeList[graphD], #[[2]] == element &]] == 0, Return[graphD]];
		parent = First[Select[EdgeList[graphD], #[[2]] == element &]][[1]];
		newDeriv = RandomDerivation[element[[1]], rules, {start,0,0}, Graph[{}]];
		newDeriv = VertexDelete[newDeriv, First[Select[VertexList[newDeriv], VertexInDegree[newDeriv, #] == 0 &]]];
		newElement = First[Select[VertexList[newDeriv], VertexInDegree[newDeriv, #] == 0 &]];
		graphD2 = EdgeAdd[graphD, Join[EdgeList[newDeriv], {parent -> newElement}]];
		deleteVertices = 
			Flatten[NestWhileList[
				With[
					{currentNodes = #},
					Flatten[
						Map[
							With[
								{node = #},
								Select[node /. #& /@ EdgeRules[graphD2], ToString[#] != ToString[node]&]
							]&,
							currentNodes
						], 
						1
					]
				]&,
				{element},
				Length[#] > 0 &
			],1];
		graphD2 = VertexDelete[graphD2, deleteVertices];
		If[Length[VertexList[graphD2]] == 1, Return[graphD]];
		Check[CodeFromDerivation[graphD2, rules], Return[graphD]];
		If[StringContainsQ[ToString[CodeFromDerivation[graphD2, rules]], "expr"], Return[graphD]];
		graphD2
	];


(* ::Section:: *)
(*Derivation graph crossover*)


DerivationGraphCrossover[rules_][graph1_, graph2_] :=
	Module[
		{commonNodes, chosenNode, childGraph, common1, common2},
		Return[RandomChoice[{graph1, graph2}]];
		If[graph1 == graph2, Return[graph1]];
		commonNodes = 
			Select[
				VertexList[graph1],
				With[
					{node1 = #},
					Length[ 
						Select[
							VertexList[graph2],
							With[
								{node2 = #},
								node1[[1]] == node2[[1]] && node1[[2]] == node2[[2]]
							]&
						]
					] > 0
				]&
			];
		commonNodes = Select[commonNodes, ToString[#[[1]]] != ToString[root] &];
		If[Length[commonNodes] == 0, Return[RandomChoice[{graph1, graph2}]]];
		chosenNode = RandomChoice[commonNodes];
		common1 = First[Select[VertexList[graph1], #[[1]] == chosenNode[[1]] && #[[2]] == chosenNode[[2]] &]];
		common2 = First[Select[VertexList[graph2], #[[1]] == chosenNode[[1]] && #[[2]] == chosenNode[[2]] &]];
		newBranch = 
			Subgraph[
				graph1,
				Flatten[
					NestWhileList[
						With[
							{currentNodes = #},
							Flatten[
								Map[
									With[
										{node = #},
										Select[node /. #& /@ EdgeRules[graph1], ToString[#] != ToString[node]&]
									]&,
									currentNodes
								], 
								1
							]
						]&,
						{common1},
						Length[#] > 0 &
					],
				1]
			];
		childGraph = ReplaceDerivationSubgraph[graph2, newBranch, common2];
		If[Length[VertexList[childGraph]] == 1, Return[RandomChoice[{graph1, graph2}]]];
		If[StringContainsQ[ToString[CodeFromDerivation[childGraph, rules]], "expr"], Return[RandomChoice[{graph1, graph2}]]];
		If[Length[Select[VertexList[childGraph], VertexInDegree[childGraph, #] > 1 &]] > 0, Return[RandomChoice[{graph1, graph2}]]];
		childGraph
	];


EndPackage[]
