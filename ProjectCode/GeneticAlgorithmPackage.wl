(* ::Package:: *)

BeginPackage["GeneticAlgorithm`"]

GeneticAlgorithm::usage =
        "Evolves a population based on the initial object optimizing the fitness function."

populationSize = 3;
numberOfGenerations = 10;

(* List of reals *)
(* ------------------ *)
RealListCrossover[rl1_, rl2_] := Mean[{rl1, rl2}];
RealListMutation[rl_] := rl + RandomReal[{-0.3, 0.3}, {Dimensions[rl][[1]]}];
(* ------------------ *)

CreateInitialPopulation[f_, initial_] := 
	NestWhile[
		Append[#, f[RandomChoice[#]]]&,
		{initial},
		Length[#] < populationSize &
	];
	
Crossover[f_][ fitness_, prev_, next_] := Append[next, f[RandomChoice[fitness->prev], RandomChoice[fitness->prev]]];
Mutation[f_][ fitness_, prev_, next_] := Append[next, f[RandomChoice[fitness->prev]]];
Copy[fitness_, prev_, next_] := Append[next, RandomChoice[fitness->prev]];
Constraint[x_] := True;

GeneticAlgorithm[initial_, FitnessF_, ConstraintFList__:{Constraint}, CrossoverF_: RealListCrossover, MutationF_: RealListMutation]:=
	Module[
		{},
		NestList[
			With[
				{population = #, fitness = FitnessF/@#},
				Print["population = ", population];
				NestWhile[
					With[
						{current = #},
						Select[
							RandomChoice[{.1, .1, .05}->{Crossover[CrossoverF], Mutation[MutationF], Copy}][fitness, population, current],
							With[{li = #}, Count[#[li]& /@ ConstraintFList, False] == 0] &
						]
					]&,
					{},
					Length[#] < populationSize &
				]
			]&,
			CreateInitialPopulation[MutationF, initial],
			numberOfGenerations
		]
	]
	
EndPackage[ ]












