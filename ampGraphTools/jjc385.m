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

graphFormatOn::usage = "Format vertexFormGraphs using doOrderedPlot on the (sorted) external legs"
graphFormatOff::usage = "Format vertexFormGraphs in the normal way (JJMC's StandardForm)"

addLoop::usage = "Adds one loop in all possible locations"
addLoopAt::usage = "Adds one loop, connecting to the given propagators"
addLegAt::usage = "Adds the given new leg to the specified old leg or propagator"

mytHat::usage = "Transforms the given propagator from 's' to 't' configuration"
myuHat::usage = "Transforms the given propagator from 's' to 'u' configuration"

isIntIsomorphic::usage = "Test whethere graphs are identical up to relabeling internal legs"


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
myIGFindIsomorphisms[gr1_,gr2_]:= (
	(* The original code fails if one graph is a multigraph and the other
		isn't.  To fix this, realize that such graphs will never be isomorphic
		and return early. *)
	If[ ! SameQ @@ MultigraphQ /@ {gr1, gr2}, Return@{} ]; (* return early if
		only one graph is a multigraph *)
	Module[{colors1,colors2},
		colors1 = Counts[Sort/@EdgeList[gr1]];
		colors2 = Counts[Sort/@EdgeList[gr2]];
		IGraphM`IGVF2FindIsomorphisms[
			{Graph@Keys[colors1],"EdgeColors"->colors1},
			{Graph@Keys[colors2],"EdgeColors"->colors2}
		]
	]
)

graphFormatOn :=
 (
  Unprotect@vertexFormGraph;
  Format[graph : vertexFormGraph[{__neckl}] ] := 
   doOrderedPlot[graph, Sort@getExtLegs@graph];
  Protect@vertexFormGraph;
  )
graphFormatOff :=
 (
  Unprotect@vertexFormGraph;
  Format[graph : vertexFormGraph[{__neckl}] ] =.;
  Protect@vertexFormGraph;
  )




(* 
* adds an internal propagator in all possible locations 
* returns list of new vertexFormGraphs
* eliminates bubbles (largely because mathematica doesn't play well \
with them)
*)
(* TODO -- option to include bubbles or not *)
(* TODO -- consider option to kill triangles *)

addLoop[ graph : vertexFormGraph[necklist : List[__neckl]], 
  loopProp_: Automatic ] :=
 Module[{edges = 
    First@concatenateNecklaces@necklist /. 
      merged[a_, b_] :> 
       First@Sort@{a, b} (*x_merged\[RuleDelayed]MapAt[Sort,x,1]*) // 
     Union},
  Table[
    addLoopAt[graph, edges[[i]], edges[[j]], loopProp ],
    {i, Length@edges},
    {j, i + 1, Length@edges}
    ] // Catenate
  ]

addLoopAt[ graph : vertexFormGraph[necklist : List[__neckl]], start_, 
  end_, loopProp_: Automatic ] := (
  (*Print@HoldForm[addLoopAt["graph",start,end,loopProp]];*)
  Module[{a, b, working = graph,
    nProps0 = 
     Length@ampGraphTools`Private`getConnectingEdges@necklist, 
    loopPropActual},
   loopPropActual = 
    If[loopProp === Automatic, in[1 + nProps0++], loopProp];
   (* collapse merged legs *)
   {a, b} = {start, end}(*/.{merged@{i_,-i_}|merged@{-i_,
   i_}\[RuleDelayed]i,merged@{i_,j_}\[RuleDelayed]i}*);
   If[! FreeQ[{a, b}, merged], Print["Problem!"]];
   working = addLegAt[working, a, loopPropActual, in[1 + nProps0++]];
   working = addLegAt[working, b, -loopPropActual, -in[1 + nProps0++]]
   ]
  )

addLegAt[ graph : vertexFormGraph[necklist : List[__neckl]], old_, 
  new_, newProp_: Automatic ] := (
  Module[{pos = Position[First@graph, old, {3}] // Map[Prepend@1], 
    nProps0 = Length@ampGraphTools`Private`getConnectingEdges@necklist,
    prop},
   prop = If[newProp === Automatic, in[nProps0 + 1], newProp];
   If[Length@pos > 1, Throw["Old leg is ambiguous"]];
   MapAt[prop &, graph, First@pos]
    // MapAt[Append[neckl@{-prop, old, new}], #, 1] &
   ]
  )




mytHat[graph_, prop_] := $jacobiReplace[graph, 
  prop, {{p1_, a_, b_}, {p2_, c_, d_}} :> {{p1, b, c}, {p2, d, a}}]

myuHat[graph_, prop_] := $jacobiReplace[graph, 
  prop, {{p1_, a_, b_}, {p2_, c_, d_}} :> {{p1, d, b}, {p2, c, a}}]

(* Sample form for rule:  {{prop1_,a_,b_},{prop2_,c_,d_}}\
\[RuleDelayed]{{prop1,b,c},{prop2,d,a}} *)
$jacobiReplace[graph : vertexFormGraph[necklist:{__neckl}], prop_, 
  rule : (_Rule | _RuleDelayed)] :=
 Catch[ 
 With[{
		(* Find positions of vertices containing `prop` and `-prop` *)
 		verts = 
         		Position[First@graph, #, {3}] & /@ {prop, -prop} 
		 		(* make sure `prop` and `-prop` each appear exactly once *)
			 	// If[Length /@ # =!= {1, 1}, 
						Throw["jacobi operator applied to non-unique propagator"], #] &
     			// Catenate
				(* make sure `prop` and `-prop` appear in separate vertices *)
				// If[First /@ # // Apply@SameQ, 
						(* Throw["jacobi operator applied to tadpole propagator"] *)
						(* Throw[ $tadpoleJacobi[graph, prop, rule], $tadpoleJacobi->"tadpoleReturn" ] *)
						Throw[ Nothing , $tadpoleJacobi->"tadpoleReturn" ]
						, #] &
				(* convert to positions in `graph` (rather than `First@graph`) *)
				// Map @ Prepend[1]
	},
   (* Rotate vertices so that `prop` and `-prop` come first *)
  RotateLeft[Extract[graph, Most@#], Last@# - 1] & /@ verts
    (* apply jacobi rule *)
    // Replace[rule]
   (* update graph with new vertices *)
   // ReplacePart[graph, Most /@ verts -> # // Thread ] &
  ],
  $tadpoleJacobi->"tadpoleReturn" ]

 


(* Check whether graphs are identical up to relabeling internal legs *)
(* this implementation relies upon listing all isomorphism between \
the two graphs *)
Options[isIntIsomorphic] = {
   (*"ignoreBubblesQ"\[Rule]True*)
   "findIsomorphismFcn" -> ampGraphTools`jjc385`myIGFindIsomorphisms
   };

isIntIsomorphic[g1_vertexFormGraph, g2_vertexFormGraph, OptionsPattern[] ] := (
  (*If[OptionValue["ignoreBubbles"]===False,Throw[
  "isIntIsomorphic:  Handling of bubbles is not implemented"]];*)
  With[{extLegs = getExtLegs /@ {g1, g2}},
   If[! SameQ @@ Length /@ extLegs, Return[False]];
   If[! SameQ @@ Sort /@ extLegs, Return[False]]; (* 
   Assumes this sorting is quicker than finding all graph isomorphisms *)
   	  OptionValue["findIsomorphismFcn"][
      mathematicaGraph /@ {g1, g2} // Apply@Sequence]
      // Select[#, 
       With[{extList = neckl@*List /@ Minus /@ getExtLegs[g1]}, 
         SameQ[extList, extList /. #]] &, 1] &
    // Length@# > 0 &
   ]
  )



End[]

EndPackage[]


