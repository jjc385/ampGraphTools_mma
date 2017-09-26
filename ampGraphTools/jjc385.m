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







End[]

EndPackage[]


