(* ::Package:: *)

Swap[state_,pair_]:=
Module[{newState},newState = state;
newState[[pair]] = newState[[Reverse[pair]]];
newState];


noOverlap[pairs_]:=AllTrue[Permutations[pairs,{2}],{}===Intersection@@#&]


PossibleSwaps[n_]:=Partition[Append[Range[n],1],2,1];


allSetsOfSwaps[n_]:=Module[{allSwaps},

(*if E=2 the number of swaps consider doesnt need to be more than 2, in general 2 should be replaced with n*)
allSwaps = Permutations[PossibleSwaps[n],3];

(*remove sets of swaps if any two of the swaps overlap*)
allSwaps = Select[allSwaps,DuplicateFreeQ[Flatten[#]]&];

(*remove duplicate sets of swaps*) 
(*sort is used so that {{1,2}{3,4}} matches with {{3,4},{1,2}}*)
allSwaps = DeleteDuplicates[allSwaps,Sort[#1]==Sort[#2]&]
]


PossibleCorrelation[state_]:=Module[{n,allSwaps,allPossibleCorrelations,tempState},
n = Length[state];
allSwaps = allSetsOfSwaps[n];

(*perform all the swaps*)
allPossibleCorrelations = 
Table[
tempState = state;
Do[
tempState = Swap[tempState,swap],
{swap,swaps}];
tempState,
{swaps,allSwaps}];

(*Remove duplicates*)
DeleteDuplicates[allPossibleCorrelations]

]


StateGraph[n_,e_]:=Module[{protoState,allStates,edges},

protoState = Table[If[i<=e,1,0],{i,n}];
allStates = Permutations[protoState];

edges = Table[
state\[DirectedEdge]correlation
,{state,allStates},
{correlation,PossibleCorrelation[state]}];

Graph[ Flatten[edges,1]]
]


AdjacencyMatrixInEnergySubspaceforEnergy[n_,e_]:=Module[{protoState,allStates,numStates,edges,stateAdjacencyMatrix,stateNum,correlationNum,numbers},
Assert[n>e];
protoState = Table[If[i<=e,1,0],{i,n}];
allStates = Permutations[protoState];
numStates = Length[allStates];
stateAdjacencyMatrix = Table[0,numStates,numStates];
numbers = Sort[Table[FromDigits[state,2],{state,allStates}]];
Do[
stateNum =Position[numbers,FromDigits[state,2]][[1]];
correlationNum = Position[numbers,FromDigits[correlation,2]][[1]];
stateAdjacencyMatrix[[stateNum,correlationNum]] = 1;
,{state,allStates},
{correlation,PossibleCorrelation[state]}];
stateAdjacencyMatrix
]


AdjacencyMatrixforEnergy[n_,e_]:=Module[{protoState,allStates,numStates,edges,stateAdjacencyMatrix,stateNum,correlationNum,numbers},
Assert[n>e];
protoState = Table[If[i<=e,1,0],{i,n}];
allStates = Permutations[protoState];
numStates = Length[allStates];
stateAdjacencyMatrix = Table[0,2^n,2^n];
Do[
stateNum =FromDigits[state,2];
correlationNum = FromDigits[correlation,2];
stateAdjacencyMatrix[[stateNum,correlationNum]] = 1;
,{state,allStates},
{correlation,PossibleCorrelation[state]}];
stateAdjacencyMatrix
]


FullAdjacencyMatrixCanonical[n_]:=Module[{protoState,allStates,numStates,edges,stateAdjacencyMatrix,stateNum,correlationNum,numbers},


stateAdjacencyMatrix = Table[0,2^n,2^n];
Do[
protoState = Table[If[i<=e,1,0],{i,n}];
allStates = Permutations[protoState];
numStates = Length[allStates];
Do[
stateNum =FromDigits[state,2];
correlationNum = FromDigits[correlation,2];
stateAdjacencyMatrix[[stateNum,correlationNum]] = 1;
,{state,allStates},
{correlation,PossibleCorrelation[state]}];
,{e,n}];
stateAdjacencyMatrix
]


FullAdjacencyMatrixEnergyBasis[n_]:=Module[{protoState,allStates,numStates,edges,stateAdjacencyMatrix,stateNum,correlationNum,numbers,index},


stateAdjacencyMatrix = Table[0,2^n,2^n];

allStates = {};
Do[

protoState = Join[Table[0,n-e],Table[1,e]];

allStates = Union[allStates,Permutations[protoState]];
,{e,0,n}];
numStates = Length[allStates];
numbers = Sort[Table[state,{state,allStates}],Total[#1]<Total[#2]&];
numbers = Table[FromDigits[num,2],{num,numbers}];


Do[

stateNum =Position[numbers,FromDigits[state,2]][[1]];
correlationNum =Position[numbers,FromDigits[correlation,2]][[1]];

stateAdjacencyMatrix[[stateNum,correlationNum]] = 1;
,{state,allStates},
{correlation,PossibleCorrelation[state]}];

stateAdjacencyMatrix
]


ClassEquivilent[s1_,s2_]:=Module[{},
MemberQ[AllEquivilentVert[s2],s1]
]
AllEquivilentVert[s_]:=Table[RotateRight[s,shift],{shift,0,Length[s]}]
ClassEquivilentEdge[e1_,e2_]:=Module[{},
ContainsAny[AllEquivilentVert[e1[[1]]],AllEquivilentVert[e2[[1]]]] ~And~ContainsAny[AllEquivilentVert[e1[[2]]],AllEquivilentVert[e2[[2]]]]
]
AllEquivilentEdges[e1_]:=Module[{},
Flatten[Outer[#1\[DirectedEdge]#2&,AllEquivilentVert[e1[[1]]],AllEquivilentVert[e1[[2]]],1]]
]


ClassEquivilentStateGraph[n_,e_]:=Module[{FullGraph,edges,verts,edgeWeights,vertWeights,representative,first,second},
FullGraph = StateGraph[n,e];
edges = {};
verts = {};

Do[
If[
representative = Intersection[verts,AllEquivilentVert[vert]];
Length[representative] == 1
,
representative = representative[[1]];
,
verts = Append[verts,vert];
]
,
{vert,VertexList[FullGraph]}];

Do[If[
first = Intersection[verts,AllEquivilentVert[edge[[1]]]][[1]];
second = Intersection[verts,AllEquivilentVert[edge[[2]]]][[1]];
edge = first\[DirectedEdge]second;
representative = Intersection[edges,AllEquivilentEdges[edge]];
Length[representative] == 1
,
edges = Append[edges,representative[[1]]];
,
edges = Append[edges,edge];]
,
{edge,EdgeList[FullGraph]}];
Graph[edges]
]


ReducedClassEquivilentStateGraph[n_,e_]:=Module[{FullGraph,edges,verts,edgeWeights,vertWeights,representative,first,second},
FullGraph = UndirectedGraph[StateGraph[n,e]];
edges = {};
verts = {};
vertWeights = <||>;

Do[
If[
representative = Intersection[verts,AllEquivilentVert[vert]];
Length[representative] == 1
,
representative = representative[[1]];
vertWeights[representative]+=1;
,
verts = Append[verts,vert];
vertWeights[vert] = 1;
]
,
{vert,VertexList[FullGraph]}];

Do[If[
	MemberQ[verts,edge[[1]]] 
	,
	
	If[MemberQ[verts,edge[[2]]],
		If[edge[[1]] != edge[[2]],
		edges = Append[edges,edge[[1]]\[DirectedEdge]edge[[2]]];
		];
		
		edges = Append[edges,edge[[2]]\[DirectedEdge]edge[[1]]];,
		second = Intersection[verts,AllEquivilentVert[edge[[2]]]][[1]];
		edge = edge[[1]]\[DirectedEdge]second;
		edges = Append[edges,edge];
		],
		
		If[MemberQ[verts,edge[[2]]],
			first = Intersection[verts,AllEquivilentVert[edge[[1]]]][[1]];
			edge = first\[DirectedEdge]edge[[2]];
			edges = Append[edges,edge];
		]
	]
	,
	{edge,EdgeList[FullGraph]}];
	Graph[edges,VertexWeight->Normal[vertWeights]]
]
