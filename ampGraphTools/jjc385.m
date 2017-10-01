(* ::Package:: *)

(* ::Subsection:: *)
(*Open*)


(* Mathematica Package *)


BeginPackage["ampGraphTools`jjc385`"]

Needs["ampGraphTools`"]


(* Exported symbols added here with SymbolName::usage *) 


StylePrint["Also loaded ampGraphTools`jjc385`, 
	Jared Claypoole's supplement"]


myAddLeg::usage = "Version of `addLeg` which will thread over lists 
	in its first argument.  
	It might be more useful to use my function `listable` instead."

listable::usage = "Repeatedly thread nth argument of a function over lists"

getLegs::usage = "Get all legs (external and internal)"
getIntLegs::usage = "Get all internal legs"

hasTriangleQ::usage = "Check whether a graph has at least one triangle"

myIGFindIsomorphisms::usage = "Find isomorphisms.  Colors edges to find multigraph isomorphisms with IGraphM"

(* ::Subsection:: *)
(* Private stuff *)

Begin["`Private`"]
(* Implementation of the package *)

(*ClearAll[myAddLeg]*)

(* Version of addLeg which will thread over lists in its first argument *)
myAddLeg[ list_List, args___ ] := myAddLeg[#, args]& /@ list
myAddLeg[ nonList_, args___ ] := Inactive[addLeg][ nonList, args ]


(* ClearAll[listable] *)
listable[f_,n_:1][args__] := 
	With[ {x = {args}[[n]] },
		If[ Head@x === List, 
			Apply[listable[f,n]]@ReplacePart[{args},n->#]& /@ x , 
			f[args]
		]
	]

(* TODO -- implement listable[f_,n_][args__] *)

ClearAll[myThread]
myThread[ f_ ][ args__ ] := (
	Thread[ Inactive[f][args], argsThread ]
		// MapAt[ First, #, 0 ]&
	)

getLegs[ graph : vertexFormGraph[necklist : {__neckl}] ] := (
	Flatten[List @@@ necklist, Range[1, 3]] 
		// Map@Replace[-x_ :> x] 
		// Union
)

getIntLegs[ graph : vertexFormGraph[necklist : {__neckl}] ] := 
	Complement[ getLegs[graph], getExtLegs[graph] ]

hasTriangleQ[ graph_vertexFormGraph ] :=
	Length @ FindCycle[ mathematicaGraph[graph], {3} ] > 0
	

(* From Alex *)
(* Essentially described here:  https://mathematica.stackexchange.com/a/97127/11035 *)
myIGFindIsomorphisms[gr1_,gr2_]:=
	Module[{colors1,colors2},
		colors1 = Counts[Sort/@EdgeList[gr1]];
		colors2 = Counts[Sort/@EdgeList[gr2]];
		IGraphM`IGVF2FindIsomorphisms[
			{Graph@Keys[colors1],"EdgeColors"->colors1},
			{Graph@Keys[colors2],"EdgeColors"->colors2}
		]
	]



End[]

EndPackage[]


