(* ::Package:: *)

(* ::Subsubsection:: *)
(*Open*)


(* Mathematica Package *)


BeginPackage["ampGraphTools`jjc385`"]

Needs["ampGraphTools`"]


(* Exported symbols added here with SymbolName::usage *) 


StylePrint["Also loaded ampGraphTools`jjc385`, 
	Jared Claypoole's supplement"]



(* ::Subsubsection:: *)
(* Some stuff *)

ClearAll[myAddLeg]

(* Version of addLeg which will thread over lists in its first argument *)
myAddLeg[ list_List, args___ ] := myAddLeg[#, args]& /@ list
myAddLeg[ nonList_, args___ ] := Inactive[addLeg][ nonList, args ]


ClearAll[listable]

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




Begin["`Private`"]
(* Implementation of the package *)



End[]

EndPackage[]


