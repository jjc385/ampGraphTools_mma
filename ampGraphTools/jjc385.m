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

myIGFindIsomorphisms::usage = "Find isomorphisms.  Colors edges to find multigraph isomorphisms with IGraphM"

graphFormatOn::usage = "Format vertexFormGraphs using doOrderedPlot on the (sorted) external legs"
graphFormatOff::usage = "Format vertexFormGraphs in the normal way (JJMC's StandardForm)"

plusMinus::usage = "plusMinus[patt] represents a pattern or minus that pattern"

addLoop::usage = "Adds one loop in all possible locations"
addLoopAt::usage = "Adds one loop, connecting to the given propagators"
addLegAt::usage = "addLegAt[g, old, new] adds the given new leg to the specified old leg or propagator"

findVertexWithLeg::usage = ""
getVertexWithLeg::usage = ""
permuteVertex::usage = ""
reverseLeg::usage = ""

mytHat::usage = "Transforms the given propagator from 's' to 't' configuration"
myuHat::usage = "Transforms the given propagator from 's' to 'u' configuration"

findIsomorphism::usage = ""
isIsomorphic::usage = "Check whether graphs are isomorphic.  Uses IGraphM."
findIntIsomorphism::usage = ""
isIntIsomorphic::usage = "Test whether graphs are identical up to relabeling internal legs"
(* findOrderedIntIsomorphism::usage = "" *)
(* isOrderedIntIsomorphic::usage = "" *)

multiLookup::usage = "looks up the value associated with the first key in keys that's present in assoc.  If no key is found, returns default "

multigraphQ::usage = ""
hasTadpoleQ::usage = ""
hasBubbleQ::usage = ""
hasTriangleQ::usage = "Check whether a graph has at least one triangle"
hasBoxQ::usage = ""

hasCycle::usage = ""
findCycle::usage = ""
findTadpoleCycle::usage = ""
findTadpoleVertices::usage = ""
tadpoleVertexQ::usage = "Checks whether a `neckl` has the form of a tadpole vertex"

nonEmptyQ::usage = "Tests whether a list (or expr with any other head) has length greater than zero.  
						Returns unevaluated for atomic input."
emptyQ::usage = "Tests whether a list (or expr with any other head) has length zero.  
						Returns unevaluated for atomic input."

reduceBy::usage = "Reduce a list to unique elements, according to the supplied
					test.  Replace non-unique elements according to some function."

jacobiOpStep::usage = "Apply jacobi operators (mytHat and myuHat) \
						to all propagators of the supplied graph"

jacobiOpUntilClosure::usage = "Apply jacobi operators (mytHat and myuHat) \
						to all propagators of the supplied graph \
						until no new graphs are generated"

jacobiOpUntilClosureSigned::usage = "Apply jacobi operators (mytHat and myuHat) \
						to all propagators of the supplied graph \
						until no new graphs are generated.
						duplicate graphs are returned with the correct sign."

$dup::usage = "Default head applied to mark duplicate graphs from jacobi stepping functions"
$zero::usage = "Default head applied to mark vanishing graphs from jacobi stepping functions"

$highlightUnorderedVerticesQ::usage = ""
doOrderedPlot::usage = "Wrapper for ampGraphTools`Private`doOrderedPlot that highlights unordered vertices"
doOrderedPlotUnhighlighted::usage = ""
getColorOrdering::usage = ""
doColorOrderedPlot::usage = ""
roughGraphPlot::usage = "Rough and ready version of graph plot"

moveGraphVertices::usage = "moveGraphVertices[g_vertexFormGraph] is a dynamic interface to reposition graph vertices"

toMom::usage = "toMom[p] converts momentum p to a canonical momentum, by multiplying by plus or minus 1"
getMomentumFromEdge::usage = "getMomentumFromEdge[edge]"
getEdgeFromMomentum::usage = "getEdgeFromMomentum[p, edgeList]"
isomReorderings::usage = "isomReorderings[ isomRuleAssocation ] associates the (re)ordering of each vertex in the new graph with the original graph's vertices"
isomSignature::usage = "isomSignature[ isomRuleAssociation ] finds the signature of the association"


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


	
myIGFindIsomorphisms[gr1_Graph,gr2_Graph,args___]:= myIGFindIsomorphisms[{gr1},{gr2}]

(* From Alex *)
(* Essentially described here:  https://mathematica.stackexchange.com/a/97127/11035 *)
(* Expects mathematica graphs as arguments *)
(* Now works if edge/vertex colors are already specified.
	Makes sure no edge colors are duplicated *)
myIGFindIsomorphisms[{gr1_Graph,opts1___},{gr2_Graph,opts2___},args___]:= (

	(* The original code fails if one graph is a multigraph and the other
		isn't.  To fix this, realize that such graphs will never be isomorphic
		and return early. *)
	If[ ! SameQ @@ MultigraphQ /@ {gr1, gr2}, Return@{} ]; (* return early if
		only one graph is a multigraph *)

	(* TODO -- be smarter about directed edges *)
	Module[{colors1,colors2},
		colors1 = Counts[Sort/@EdgeList[gr1]];
		colors2 = Counts[Sort/@EdgeList[gr2]];

		If[ Length@Catenate[FilterRules[#,"EdgeColors"]& /@ {{opts1},{opts2}}]==0,	

			(* No special processing required *)
			IGraphM`IGVF2FindIsomorphisms[
				{Graph@Keys[colors1],"EdgeColors"->colors1, opts1},
				{Graph@Keys[colors2],"EdgeColors"->colors2, opts2}
			],

			(* properly merge options *)

(* 
			compositeColors1 =
			With[ { colorOpts1 = FilterRules[opts1,"EdgeColors"]},
				{ Lookup[colors1,#], multiLookup[colorOpts1, {#,Reverse@#}, 0] } &
					/@ Keys@colors1
			]
*)
			(* {{{ *)
			(* Make sure neither (1) color values nor (2) multigraph color keys (i.e., edges to be colored) are duplicated, for each graph*)
			(* 1 -- check color values *)
			Module[ {
				allMultiColors = Values /@ { colors1, colors2 } // Catenate,
				allOptsColors = Values@Lookup[#,"EdgeColors",{}]& /@ {{opts1},{opts2}} // Catenate
				},

				If[ Length @ Intersection[ allMultiColors, allOptsColors ] != 0,
					Throw[ "myIGFindIsomorphisms:  specified edge colors incompatible with multigraph colorings"]
				]
			];
			(* 2 -- check color keys (i.e., edges to be colored) *)
			Module[ {
				colorKeys1 = Map[Sort]@*Keys /@ { Select[colors1,#>1&], Lookup[{opts1}, "EdgeColors",{}] },
				colorKeys2 = Map[Sort]@*Keys /@ { Select[colors2,#>1&], Lookup[{opts2}, "EdgeColors",{}] }
				},

				If[ Length @ Intersection@@ colorKeys1 != 0,
					Throw[ "myIGFindIsomorphisms:  multigraph edges were assigned colors" ]
				]
			];
			(* }}} *)

			(* now that colors have been shown to be compatible, attempt to combine them *)
			Module[{newColors1, newColors2},
				newColors1 = 
					Append[ colors1, 
						KeyMap[Sort]@Association@Lookup[{opts1},"EdgeColors"]
					];
				newColors2 = 
					Append[ colors2, 
						KeyMap[Sort]@Association@Lookup[{opts2},"EdgeColors"]
					];
										


				IGraphM`IGVF2FindIsomorphisms[
					{Graph@Keys[colors1],"EdgeColors"->newColors1, opts1},
					{Graph@Keys[colors2],"EdgeColors"->newColors2, opts2},
					args
				]
			]
		]


	]
)




(* looks up the value associated with the first key in keys that's \
present in assoc.  If no key is found, returns default *)
multiLookup[assoc_, keys_List, default_: Automatic] :=
 $multiLookup["$multLookupDummy", assoc, keys, default]

$multiLookup[
  prev : Except@(_Missing | "$multLookupDummy"), ___] := prev
$multiLookup[prev_, assoc_, keys : {}, default_] :=
 Switch[default,
  Automatic, prev,
  _, default
  ]
$multiLookup[prev_, assoc_, keys_List, default_] := $multiLookup[
  Lookup[assoc, First@keys], assoc, Rest@keys, default]







graphFormatOn :=
 (
	$graphFormatOnQ := True;
(* 	$graphFormatTooltipQ = True; *)
  Unprotect@vertexFormGraph;
(* 
  Format[graph : vertexFormGraph[{__neckl}] ] /; $graphFormatOnQ := 
*) 
  Format[graph : vertexFormGraph[{__neckl}] ] := 
(* 		Tooltip[doOrderedPlot[graph, Sort@getExtLegs@graph], *)
		Tooltip[doOrderedPlot[graph],
			Block[{$graphFormatOnQ=False},InputForm@graph] 
		];
  Protect@vertexFormGraph;
  )
graphFormatOff :=
 (
	$graphFormatOnQ := False;
(* 	$graphFormatTooltipQ = False; *)
  Unprotect@vertexFormGraph;
  Format[graph : vertexFormGraph[{__neckl}] ] =.;
  Protect@vertexFormGraph;
  )



plusMinus[patt_]:= (patt | -patt)

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
    addLoopAt[graph, edges[[i]], edges[[j]], "loopProp"->loopProp ],
    {i, Length@edges},
    {j, i + 1, Length@edges}
    ] // Catenate
  ]

Options[addLoopAt] = {"loopProp"->Automatic, "rightHandedQ"->Automatic}
addLoopAt[ graph : vertexFormGraph[necklist : List[__neckl]], 
	(start_->startOpt_)|start_, (end_->endOpt_)|end_, OptionsPattern[] ] := (
  Module[{a, b, working = graph,
    nProps0 = 
     		Max[0,Cases[getIntLegs@graph,plusMinus[in[n_Integer]]:>n]],
    loopProp=OptionValue["loopProp"],
	rightHandedQ=OptionValue["rightHandedQ"],
	propA = If[ nonEmptyQ@{startOpt}, First@{startOpt}, Automatic ],
	propB = If[ nonEmptyQ@{endOpt}, First@{endOpt}, Automatic ]
	},
   loopProp = 
    If[loopProp === Automatic, in[++nProps0], loopProp];
	rightHandedQ = Switch[ rightHandedQ,
		Automatic, {True,True},
		True, {True,True},
		False, {False,False},
		First|Most, {True, False},
		Last|Rest, {False, True},
		_, rightHandedQ
	];
	propA = Switch[ propA,
		Automatic, in[++nProps0],
		"reversed", -in[++nProps0],
		_, propA 
	];
	propB = Switch[ propB,
		Automatic, in[++nProps0],
		"reversed", -in[++nProps0],
		_, propB 
	];
   (* collapse merged legs *)
   {a, b} = {start, end}(*/.{merged@{i_,-i_}|merged@{-i_,
   i_}\[RuleDelayed]i,merged@{i_,j_}\[RuleDelayed]i}*);
   If[! FreeQ[{a, b}, merged], Print["Problem!"]];
   working = addLegAt[working, a->propA, loopProp, "rightHandedQ"->First@rightHandedQ];
   working = addLegAt[working, b->propB, -loopProp, "rightHandedQ"->Last@rightHandedQ]
   ]
  )

Options[addLegAt] = { 
	(*    		"newProp" -> Automatic,  *)
   		"rightHandedQ" -> Automatic 
   };
addLegAt[ graph : vertexFormGraph[necklist : List[__neckl]], (old_ -> oldOpt_) | old_(*:Except[_Rule]*), 
	new_, OptionsPattern[] ] := (
  	Module[{pos = Position[First@graph, old, {3}] // Map[Prepend@1], 
    	nProps0 =
     		Max[0,Cases[getIntLegs@graph,plusMinus[in[n_Integer]]:>n]],
		prop = If[ nonEmptyQ@{oldOpt}, First@{oldOpt}, Automatic ],
(*     	prop = OptionValue@"newProp", *)
		rightHandedQ = OptionValue@"rightHandedQ"
  		},
   	prop = Switch[ prop,
	   	Automatic, in[nProps0+1],
	   	"reversed", -in[nProps0+1],
	   	_, prop
   	];
   	rightHandedQ = Switch[ rightHandedQ,
	   	Automatic, True,
	   	_, rightHandedQ
   	];
   	If[Length@pos > 1, Throw["addLegAt: Old leg is ambiguous"]];
   	If[Length@pos == 0, Throw["addLegAt: Old leg not found"]];
   	MapAt[prop &, graph, First@pos]
   	// MapAt[Append[neckl@If[TrueQ@rightHandedQ, {-prop, old, new}, {-prop, new, old}]], #, 1] &
	]
)


findVertexWithLeg[ g_vertexFormGraph, leg_ ] :=
	With[ {posRaw = Position[ First@g, leg, {3} ]},
		If[ Length@posRaw > 1, 
			Throw["findVertexWithLeg:  Non-unique leg specified"]];
		Prepend[1]@First@posRaw
		// Drop[#, -2]&
	]

getVertexWithLeg[ g_vertexFormGraph, leg_ ] :=
	Extract[ g, findVertexWithLeg[g, leg] ]

permuteVertex[ g_vertexFormGraph, leg_ ] :=
	Module[{vpos, vertLength},
		vpos = findVertexWithLeg[g, leg];
		vertLength = Length@First@Extract[g, vpos];
		MapAt[ #[[ Catenate@{{2,1},Range[3,vertLength]} ]] &, g, Append[1]@vpos ]
	]

permuteVertex[ g_vertexFormGraph, legList_List ] :=
	Fold[ permuteVertex, g, legList ]

reverseLeg[ g_vertexFormGraph, leg_ ] :=
	MapAt[ Replace[ #, leg -> -leg, {1,2} ]&, g, {1,;;,1} ]

reverseLeg[ g_vertexFormGraph, legList_List ] :=
	Fold[ reverseLeg, g, legList ]



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
						Throw["jacobi operator applied to non-unique or 
							non-existent propagator, or to external leg"], #] &
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

(* default to one *)
findIsomorphism[ g1_vertexFormGraph, g2_vertexFormGraph, n_:1, args___ ] :=
	IGraphM`IGVF2FindIsomorphisms[ Sequence @@ mathematicaGraph /@ {g1, g2}, n, args ]

(* default to all *)
findIsomorphisms[ g1_vertexFormGraph, g2_vertexFormGraph, n_:All, args___ ] :=
	IGraphM`IGVF2FindIsomorphisms[ Sequence @@ mathematicaGraph /@ {g1, g2}, n, args ]
 
(* Check whether graphs are isomorphic *)
(* Uses IGraphM methods *)
 (* isIsomorphic = myIGFindIsomorphisms[ mathematicaGraph /@ {#1, #2} // Apply[Sequence], ##3 ] & *)
isIsomorphic[ g1_vertexFormGraph, g2_vertexFormGraph ] :=
	IGraphM`IGIsomorphicQ @@ mathematicaGraph /@ {g1, g2}


(* Check whether graphs are identical up to relabeling internal legs *)
(* this implementation relies upon listing all isomorphism between \
the two graphs *)
Options[isIntIsomorphic] = {
   "findIsomorphismFcn" -> ampGraphTools`jjc385`myIGFindIsomorphisms
   };

isIntIsomorphic[g1_vertexFormGraph, g2_vertexFormGraph, opts:OptionsPattern[] ] := (
	findIntIsomorphism[ g1, g2, 1, opts ]
    // Length@# > 0 &
)

Options[findIntIsomorphism] = {
   "findIsomorphismFcn" -> ampGraphTools`jjc385`myIGFindIsomorphisms,
   "graphOutList" -> None,
   "fixedLegList" -> Automatic, (* if specified, overrides fixedLegFcn *)
   "fixedLegFcn" -> Automatic
   };
findIntIsomorphism[g1_vertexFormGraph, g2_vertexFormGraph, n:(_Integer?Positive|Infinity|All):1, OptionsPattern[] ] := Module[
	{
	fixedLegList=OptionValue["fixedLegList"],
	fixedLegFcn=OptionValue["fixedLegFcn"],
	explicitFixedLegListQ=False
	},
	fixedLegList = Switch[ fixedLegList,
		_List, explicitFixedLegListQ=True; fixedLegList,
		Automatic|_, {}
	];
	fixedLegFcn = Switch[ fixedLegFcn,
		Automatic, getExtLegs,
		_, fixedLegFcn
	];

  (*If[OptionValue["ignoreBubbles"]===False,Throw[
  "isIntIsomorphic:  Handling of bubbles is not implemented"]];*)
  Module[{fixedLegs = If[!explicitFixedLegListQ, fixedLegFcn /@ {g1, g2}, fixedLegList&/@{1,2}] },
	If[ !explicitFixedLegListQ,
   If[! SameQ @@ Length /@ fixedLegs, Return[False]];
   If[! SameQ @@ Sort /@ fixedLegs, Return[False]]; (* 
   Assumes this sorting is quicker than finding all graph isomorphisms *)
	];
	With[{mmaGraphList = mathematicaGraph /@ {g1, g2} },
		If[ MatchQ[ OptionValue["graphOutList"], Hold[_Symbol] ], 
	   		OptionValue["graphOutList"] /. Hold[l_Symbol] :> (l=mmaGraphList) 
		];
   	OptionValue["findIsomorphismFcn"][mmaGraphList // Apply@Sequence]
      // Select[#, 
	With[{extList = neckl@*List /@ Minus /@ First@fixedLegs}, 
         SameQ[extList, extList /. #]] &, n/.All->Infinity] &
   ]
  ]
  ]


(* 
findOrderedIntIsomorphism[g1_vertexFormGraph, g2_vertexFormGraph, n:(_Integer?Positive|Infinity|All):1, OptionsPattern[] ] := (
	findIntIsomorphism[g1,g2,n]
	// Select[#,

)
*)

multigraphQ[ g_vertexFormGraph ] :=
	MultigraphQ @@ mathematicaGraph[g]

$tadpoleVertexPattern = neckl[{___, a_, ___, -a_, ___}]|neckl[{___, -a_, ___, a_, ___}]

hasTadpoleQ[ g_vertexFormGraph ] :=
(* 	FreeQ[ g, $tadpoleVertexPattern ]  *)
	nonEmptyQ @ findTadpoleCycle[ g, 1 ]

hasBubbleQ[ g_vertexFormGraph ] :=
	nonEmptyQ @ FindCycle[ mathematicaGraph[g], {2}, 1 ]

hasTriangleQ[ g_vertexFormGraph ] :=
	nonEmptyQ @ FindCycle[ mathematicaGraph[g], {3}, 1 ]

hasBoxQ[ g_vertexFormGraph ] :=
	nonEmptyQ @ FindCycle[ mathematicaGraph[g], {4}, 1 ]

nonEmptyQ[ expr_?(Not@*AtomQ) ] := Length @ expr > 0
emptyQ[ expr_?(Not@*AtomQ) ] := Length @ expr == 0

(* FindCycles-like output of tadpoles *)
(* Here a tadpole is any propagator whose two ends connect to the same vertex *)
findTadpoleCycle[ g:vertexFormGraph[necklist:{___neckl}], s_:1 ] :=
	findTadpoleVertices[ g, s ] // Map[ # <-> # & ]

findTadpoleVertices[ vertexFormGraph[necklist:{___neckl}], s_:1 ] :=
	Cases[ necklist, $tadpoleVertexPattern, 1, s ]

tadpoleVertexQ[ v:neckl[_List] ] := MatchQ[ v, $tadpoleVertexPattern ]
	

(* like built-in FindCycle, but counts tadpoles as cycles of length 1 *)
(* Looks for tadpole cycles first *)
findCycle[ g_vertexFormGraph ] := findCycle[ g, Infinity ]
findCycle[ g_vertexFormGraph, kspec:(1|{1,1}), s:1 ] :=
	findTadpoleCycle[ g, s ]
findCycle[ g_vertexFormGraph, kspec: ( (a_Integer /; a>0) | {1} | ({a:1, b_Integer} /; b>=a) ), s_:1 ] :=
	With[ {tadpoles = findTadpoleCycle[ g, s ]},
		If[ Length@tadpoles >= s, 
			Take[tadpoles, s],
			Join[ tadpoles, FindCycle[ mathematicaGraph@g, kspec, s-Length@tadpoles ] ]
		]
	]
findCycle[ g_vertexFormGraph, kspec: ( ({a_Integer, b_Integer} /; a>1 && b>=a) | ({a_Integer}/;a>1) ), s:1 ] :=
	FindCycle[ mathematicaGraph@g, kspec, s ]

hasCycle[ g_vertexFormGraph, kspec_ ] := nonEmptyQ @ findCycle[ g, kspec, 1 ]


	

ClearAll[reduceBy]
Options[reduceBy] = {
	"duplicateFcn" -> None,
	"knownElements" -> Automatic,
	"knownClassFcn" -> None,
	"sowQ" -> True,
	"extraSameTestArgsQ" -> False
}
reduceBy[ list_, sameTest:Except[_Rule|_RuleDelayed]:Equal, levSpec:(_Integer|{__Integer}):{1}, OptionsPattern[] ] := 
	Module[{knownElements=OptionValue["knownElements"], 
			duplicateFcn=OptionValue["duplicateFcn"],
			knownClassFcn=OptionValue["knownClassFcn"],
			knownClassesQ=False,
			sameTestFullQ = OptionValue@"extraSameTestArgsQ",
			sameTestFirst,
			sameTestRest,
			sameTestFull,
			temp
			},
		knownClassFcn = Switch[knownClassFcn,
			None|Automatic, None,
			_, (knownClassesQ=True); knownClassFcn
		];
  		knownElements = Switch[knownElements,
    		None|Automatic, If[TrueQ@knownClassesQ, <||>, {}],
    		Hold[_Symbol], First@knownElements,
    		_, knownElements
    	];
  		duplicateFcn = Switch[duplicateFcn,
			None, (Nothing &),
			Automatic, $dup,
			_, duplicateFcn
		];
		If[ sameTestFullQ,
			sameTestFirst = First;
				sameTestRest = Rest,
			sameTestFirst = Identity,
				sameTestRest = {}
		];
       	Map[
			If[ knownClassesQ,
				Function[g,
					With[{class=knownClassFcn@g},
						If[
							(temp=Lookup[ knownElements, Key@class, {} ]
							// Select[ #, sameTestFirst@(sameTestFull=sameTest[#, g]) &, 1] & )
							// nonEmptyQ,
							duplicateFcn[First@temp, g, sameTestRest@sameTestFull//Apply[Sequence] ],
							If[KeyExistsQ[knownElements,class],
								AppendTo[ knownElements[class], g ],
								knownElements[class]={g}
							];
							g
						]
					]
					//Sow[#,"elemOut"]&
				],
				Function[g,
					If[
						Length@(temp =
						Select[knownElements, sameTestFirst@(sameTestFull=sameTest[#, g]) &, 1]
						) > 0,
						duplicateFcn[First@temp, g, sameTestRest@sameTestFull//Apply[Sequence] ],
						AppendTo[knownElements, g]; g
					]
					//Sow[#,"elemOut"]&
				]
			],
			list,
			levSpec
		]
		// (If[ TrueQ@OptionValue["sowQ"], Sow[knownElements, "reduceBy"->"knownElementsFinal"]];#)&
		(* If list was passed by reference, update the reference list *)
		// (If[MatchQ[OptionValue["knownElements"], Hold[_Symbol]],
     			OptionValue["knownElements"] /. 
    				Hold[l_Symbol] :> (l = knownElements);
				]; # )&
	]


Options[jacobiOpStep] = {
   "reduceGraphsQ" -> True,(* eliminate duplicate graphs from output *) 
   "knownGraphs" -> Automatic,
   "duplicateGraphFcn" -> Automatic,
   "vanishingGraphFcn" -> Automatic,
   "duplicateGraphTest" -> isIsomorphic,
   "vanishingGraphTest" -> (hasCycle[#,3]&),
   "graphClassFcn" -> None,
   "propPattToAvoid" -> plusMinus@_l,
   "extraSameTestArgsQ"->False
   };
Print["ampGraphTools`jjc385`jacobiOpStep:  Warning -- labeled loop momenta are simply ignored when generating Jacobi relations."];
jacobiOpStep[graph : _vertexFormGraph, OptionsPattern[] ] :=
 Module[{knownGraphs = OptionValue["knownGraphs"], 
   	duplicateFcn = OptionValue["duplicateGraphFcn"], 
   	vanishingFcn = OptionValue["vanishingGraphFcn"], 
	vanishingTest = OptionValue["vanishingGraphTest"],
	graphClassFcn = OptionValue["graphClassFcn"],
	graphClassesQ = False,
	temp},
  graphClassFcn = Switch[graphClassFcn,
  	None|Automatic, None,
  	_, graphClassesQ = True; graphClassFcn
  ];
  knownGraphs = Switch[knownGraphs,
    None, If[graphClassesQ, <||>, {}],
    Automatic, If[graphClassesQ, <|graphClassFcn@graph->{graph}|>, {graph}],
    Hold[_Symbol], First@knownGraphs,
    _, knownGraphs
    ];
  duplicateFcn = Switch[duplicateFcn,
 	None, (# &),
	Automatic, $dup,
    _, duplicateFcn
    ];
  vanishingFcn = Switch[vanishingFcn,
	"kill", Nothing,
 	None, (# &),
	Automatic, $zero,
    _, vanishingFcn
    ];
	vanishingTest = Switch[vanishingTest,
		Automatic, (hasCycle[#,3]&),
		_, vanishingTest
	];

(*   Catenate@ *)
	(*       Association@Table[ prop -> Association@Table[ op -> op[graph, prop], {op, {mytHat, myuHat}} ], {prop, getIntLegs@graph} ] *)
      Table[  <| "prop"->prop, "op"->op |> -> op[graph, prop], 
	  		{op, {mytHat, myuHat}}, 
	  		{prop, Cases[getIntLegs@graph, Except@OptionValue@"propPattToAvoid"] } 
	  ]
	  // Catenate // Association
	  //Sow[#,"debug"->"toVanishTest"]&
	  // Map[ If[ TrueQ@vanishingTest@#, vanishingFcn@#, # ] &, #, {1} ]&
	  //Sow[#,"debug"]&
	  //DeleteCases[#, Nothing]&
	  //Sow[#,"toReduce"]&
     // If[TrueQ@OptionValue["reduceGraphsQ"], 
			reduceBy[ #, OptionValue["duplicateGraphTest"], {1},
	   			"knownElements"->Hold@knownGraphs, 
				"duplicateFcn"->duplicateFcn,
				"knownClassFcn"->graphClassFcn,
				"extraSameTestArgsQ"->OptionValue@"extraSameTestArgsQ"
	   		]
       		,#
		] &
    // (Sow[knownGraphs, jacobiOpStep -> "knownGraphsEnd"]; #) &
   // If[MatchQ[OptionValue["knownGraphs"], Hold[_Symbol]],
     OptionValue["knownGraphs"] /. 
      Hold[l_Symbol] :> (l = knownGraphs); #
     , #] &
  ]


Options[jacobiOpUntilClosure] = 
		{"maxIterationDepth" -> Infinity,
		"reduceGraphsQ" -> True, (* Changing this is not recommended *)
		"vanishingGraphTest" -> Automatic,
		"duplicateGraphTest" -> isIntIsomorphic,
		"vanishingGraphFcn" -> "kill",
		"killDuplicatesQ" -> True,
		"duplicateGraphFcn" -> $dup,
   		"graphClassFcn" -> None,
   		"propPattToAvoid" -> plusMinus@_l,
   		"extraSameTestArgsQ"->False
		}
jacobiOpUntilClosure[graph_vertexFormGraph, OptionsPattern[] ] :=
 Module[{knownGraphs, jacobiEdges = <||>, 
   	jacobiStepGraphFcn, jacobiStepListFcn, jacobiInstance},
	knownGraphs = If[ MatchQ[OptionValue["graphClassFcn"], None|Automatic], 
						List@graph, 
						<|OptionValue["graphClassFcn"]@graph->{graph}|>
					];
  Block[{$dup},
   jacobiStepGraphFcn =
    (* expects a vertexFormGraph as an argument *)
    Module[{newList},
      (* produce a new list of `graph -> { related graphs }` edges *) 
      # -> (newList = 
          jacobiOpStep[#, "knownGraphs" -> Hold@knownGraphs, 
		   "reduceGraphsQ" -> OptionValue["reduceGraphsQ"],
		   (* TODO -- hack *)
		   "duplicateGraphFcn" -> OptionValue["duplicateGraphFcn"],
           "duplicateGraphFcn" ->
		   If[!TrueQ@OptionValue["killDuplicatesQ"],($dup[#] &),(Nothing[#] &)],
		   "duplicateGraphTest" -> OptionValue["duplicateGraphTest"],
		   "vanishingGraphTest" -> OptionValue["vanishingGraphTest"],
		   "vanishingGraphFcn" -> OptionValue["vanishingGraphFcn"],
   		   "graphClassFcn" -> OptionValue["graphClassFcn"],
   		   "propPattToAvoid" -> OptionValue["propPattToAvoid"],
		   "extraSameTestArgsQ"->OptionValue["extraSameTestArgsQ"]
	   ])
       (* append those edges to `jacobiEdges` *)
       // (AssociateTo[jacobiEdges, #] &);
(*       Catenate @ newList *)
		Values @ newList  // Sow[#,"debug"]&
      ] &;
   jacobiStepListFcn =
	(* Now expects a flat list of lists as an argument (and maybe it always did) *)
	   (* 	(* now expects an association of associations as an argument *) *)
    (* used to expect a list of lists as an argument *)
    (
	  (* 	(Map[Normal, #, {0,1} ] &) /* *) (* Convert to a list of lists *)
     Map[jacobiStepGraphFcn] /* 
     Catenate /*  
	 (Sow[#,"debug2"]&) /*
	 (Replace[#, _$dup | _$zero -> Nothing, 1] &)
     );
   Internal`InheritedBlock[{jacobiOpStep},
    jacobiOpStep[
      x : _$dup | _$zero | _$tadpoleJacobi, ___] := x;
    
(*     NestWhile[jacobiStepListFcn /* Sow[#, jacobiInstance->"nextLevel"]& , *)
     NestWhile[jacobiStepListFcn /* ((Print["nextLevel"];#)&),
   			{graph}, Length@# > 0 &, 1, 
     OptionValue@"maxIterationDepth"];
    jacobiEdges
    ]
   ]
  ]


Options[jacobiOpUntilClosureSigned] = 
		{"maxIterationDepth" -> Infinity,
		"reduceGraphsQ" -> True, (* Changing this is not recommended *)
		"vanishingGraphTest" -> Automatic,
		"vanishingGraphFcn" -> "kill",
		"killDuplicatesQ" -> True,
		"duplicateGraphFcn" -> $dup,
   		"graphClassFcn" -> None,
   		"propPattToAvoid" -> plusMinus@_l,
		"findIsomFcn" -> findIsomorphism, (* function which returns a list of isomorphisms -- only the first will be used *)
		"postProcessFcn" -> Automatic
		};
jacobiOpUntilClosureSigned[graph_vertexFormGraph, opts:OptionsPattern[] ] :=
	Module[{
		findIsomFcn=OptionValue@"findIsomFcn",
		postProcessFcn = OptionValue@"postProcessFcn"
		},
		postProcessFcn = Switch[ postProcessFcn,
			Full, Map[ Replace[ $dup[a_,_,_,sign_]:>sign*a ], #, {2} ]& ,
			Automatic, Map[ Replace[ $dup[a_,b_,_,sign_]:>sign*$dup[a,b] ], #, {2} ]& ,
			"sign", Map[ Replace[ $dup[a_,b_,isom_,sign_]:>sign*$dup[a,b,isom] ], #, {2} ]& ,
			None, Identity,
			_, postProcessFcn
		];
		jacobiOpUntilClosure[ graph, 
			FilterRules[{opts},Options@jacobiOpUntilClosure],
			"duplicateGraphTest" -> (With[{isom = Replace[#, {x_, ___} :> x]}, {nonEmptyQ@#, isom, 
				isomSignature@isom}] &)@*findIsomFcn ,
			"extraSameTestArgsQ" -> True
		]
		//postProcessFcn
	]






(* definition:  toMom *)
With[{complexityFcn = Simplify`SimplifyCount},
 	toMom[p_] := With[{old = complexityFcn@p, new = complexityFcn@(-p)},
   		Which[
			new < old, -p,
			old < new, p,
			old == new, First@Sort@{p, -p},
			True, p
		]
   	]
]

Options[getMomentumFromEdge] =
  {
   "alignEdge" -> True (* 
   Align momentum to point along supplied edge (True) or convert to \
canonical momentum (False) *)
   };
getMomentumFromEdge[h_[v1_, v2_], 
   OptionsPattern[] ] /; (MatchQ[#, neckl@{__}] & /@ {v1, v2} // 
    Apply@And) := Module[{reapTag, realignMomQ},
  realignMomQ = Switch[OptionValue@"alignEdge",
    True | Automatic | "supplied", False (* 
    keep aligned with supplied edge *) ,
    		_ | "canon" | "canonical", True (* 
    convert to canonical momentum *)
    ];
  Reap[First /@ {v1, v2} //. {
         (*{{a1___,a_,a2___},{b1___,-a_,b2___}}:>(Sow[a,reapTag];{{a1,
         a2},{b1,b2}}),
         {{a1___,-a_,a2___},{b1___,a_,b2___}}:>(Sow[-a,reapTag];{{a1,
         a2},{b1,b2}}) *)
         {{a1___, a_, a2___}, {b1___, b_, b2___}} /; 
           a === -b :> (Sow[a, reapTag]; {{a1, a2}, {b1, b2}})
         },
       reapTag]
      // Last // First
    // If[Length@# != 1, Print["multiple momenta found"]; $Failed@#, 
      First@#] &
   // If[realignMomQ, toMom@#, #] &
  ]


getEdgeFromMomentum[mom_, g_Graph, args___] := 
 getEdgeFromMomentum[mom, VertexList@g(*vertList_List*), args]

Options[getEdgeFromMomentum] = {
   "alignEdge" -> True (* 
   Align edge to point with supplied momentum (True) or canonical \
momentum (False) *)
   };

getEdgeFromMomentum[mom_, vertList_List, OptionsPattern[] ] :=
 Module[{posList = Position[vertList, mom | -mom, {3}], realignEdgeQ},
  realignEdgeQ = Switch[OptionValue@"alignEdge",
    True | Automatic | "supplied", False (* 
    keep aligned with supplied momentum *) ,
    _ | "canon" | "canonical", True (* 
    realign with canonical momentum *)
    ];
  If[Length@posList != 2, 
   Throw["getEdgeFromMomentum:  consistency error.  Bad momentum."]];
  Extract[vertList, Take[#, 1]] & /@ 
     If[MatchQ[Extract[vertList, First@posList], mom], posList, 
      Reverse@posList]
    // Apply[Rule]
   // If[! TrueQ@OptionValue@"alignEdge",
     (* align edge with canonical momentum *)
     If[mom === toMom@mom,
      #,
      Reverse@#
      ]
     ,
     (* align edge with supplied momentum (i.e., leave as is) *)
     #
     ] &
  ]

cyclicPermQ[{}] := True
cyclicPermQ[{1}] := True
cyclicPermQ[list_List] /; ! MemberQ[list, 1] := False
cyclicPermQ[list_List] := 
 With[{temp = RotateLeft[list, FirstPosition[list, 1] - 1]}, 
  temp === Range@Length@temp]




(* assumes association maps all vertices of g1 to g2, including \
external edge vertices *)
isomReorderings[ isomAssoc_Association ] := Module[{
   verts1 = Keys@isomAssoc,
   verts2 = Values@isomAssoc,
   fProcessVert,
   dests1,
   dests2,
   dests1prime,
   reorderings
   },
  
  fProcessVert[allVerts_List ][vert : neckl[pList : {__}]] := 
   Module[{},
    (* convert list of ougoing momenta to a list of connecting \
vertices *)
     # -> First@Cases[allVerts, neckl@{___, -#, ___}] & /@ pList
    ];
  
  
  {dests1, dests2} =
   fProcessVert[#] /@ # & /@ {verts1, verts2}
    // Map[Values];
  
  dests1prime = Replace[dests1, isomAssoc, {2}];
  
  reorderings = Transpose@{dests1prime, dests2}
    (*//Replace[#,x_neckl\[RuleDelayed]First@x,{3}]& (* 
    get rid of neckl heads *)*)
    (*//Map[(PermutationList)@*Apply[FindPermutation]]*)
    // Map[
     Ordering@
       PermutationList[Apply[FindPermutation, #], Length@First@#] &]
  ;
  
  Thread[Normal@isomAssoc -> reorderings]
   // Association
  
  
  
  ]


(* 
	Now defaults to returning +/- 1, or 0
Returns number of acyclic permutations of cubic vertices required \
in the isomorphism.
If an acyclic permutation of a vertex with more than 3 legs is \
required, returns +/- infinity (+ if overall permutation is even, - \
if odd) *)
Options[isomSignature] = {
	"outputForm" -> "plusMinus", (* vs "nSwaps" *)
   "isomReorderingsOut" -> None
   };
isomSignature[isomAssoc_Association] := With[
  	{reorderings = isomReorderings@isomAssoc,
		refineOutputQ = Switch[ OptionValue@"outputForm",
			"nSwaps"|"nswaps"|Full, False,
			"plusMinus"|"plusMinus"|Automatic|_, True
		]
	},
  If[MatchQ[OptionValue@"isomReorderingsOut", Hold[_Symbol]], 
   Replace[OptionValue@"isomReorderingsOut", 
    Hold[s_Symbol] :> (s = reorderings)]
   ];
  
  reorderings
       // Values
      // Select[Not@*cyclicPermQ]
     // GroupBy[Length@# == 3 &]
    (*//{
    (* cubic vertices with odd perms *)
    Length@Lookup[#,True,{}],
    (* non-cubic verts with odd perms *)
    Length@Lookup[#,False,{}]
    }&*)
    // Map[Length]
   (*//Lookup[#,False,0]&*)
   // If[Lookup[#, False, 0] === 0,
     Lookup[#, True, 0],
     Power[-1, Apply[Plus]@Values@#]*Infinity
     ] &
	// If[ refineOutputQ,
			If[ IntegerQ@#, Power[-1, #], 0],
			#
		]&
  
  
  ]






doOrderedPlot[ graph_ ] :=
(* 	doOrderedPlot[ graph, Sort@getExtLegs@graph ] *)
	doOrderedPlot[ graph, getColorOrdering@graph ]

$highlightUnorderedVerticesQ = True;

doOrderedPlot[ graph_, args__ ] := (
	doOrderedPlotUnhighlighted[ graph, args ]
	// If[$highlightUnorderedVerticesQ, highlightUnorderedVertices, Identity]
)


doOrderedPlotUnhighlighted[ graph_, args___ ] :=
	ampGraphTools`Private`doOrderedPlot[ graph, args ]

getColorOrdering[graph : vertexFormGraph[necklist : List[__neckl]], 
  startLeg_: k@1] := 
 Module[{orderedExtLegs = 
    First@concatenateNecklaces@necklist /. _merged :> Nothing },
  RotateLeft[ orderedExtLegs, 
   First@First@Position[orderedExtLegs, startLeg] - 1 ]
  ]

doColorOrderedPlot[g_vertexFormGraph, startLeg_: k@1] := 
 doOrderedPlot[g, getColorOrdering[g, startLeg]]

(* highlight unordered vertices in ordered plots *)
highlightUnorderedVertices[
  GG : Graphics[
    Annotation[
     GraphicsGroup[{ arrows_List, gc_GraphicsComplex }, argsGG___], 
     argsA___], argsG___]] := With[{ngc = Normal@gc},
  Position[gc, Tooltip[pt_Point, vert_neckl]]
         // 
         AssociationMap[
          Replace[Tooltip[{pt_Point}, 
              vert_neckl] :> (vert -> pt)]@*(Extract[ngc, #] &)@*Rest]
        // getVertexSegmentsFromVertexPoints
       // Select[Not]
      // Keys
     // Map@Append[1]
    // MapAt[{Red, PointSize[Large], #} &, gc, #] &
   // Graphics[
     Annotation[GraphicsGroup[{ arrows, # }, argsGG], argsA], argsG] &
  ]

getVertexPointsFromOrderedPlot[
  	GG : Graphics[
    	Annotation[
     		GraphicsGroup[{ arrows_List, gc_GraphicsComplex }, argsGG___], 
     			argsA___], argsG___]
 	] := With[{ngc = Normal@gc},
  Position[gc, Tooltip[pt_Point, vert_neckl]]
   // AssociationMap[
    Replace[Tooltip[{pt_Point}, 
        vert_neckl] :> (vert -> pt)]@*(Extract[ngc, #] &)@*Rest]
  ]

(* TODO -- need to implement special handling of tadpole vertices *)
getVertexSegmentsFromVertexPoints[(*vpList:{(_neckl\[Rule]_Point)..}*)
  vpList : KeyValuePattern[_ -> (_neckl -> _Point)]] := (
  Module[{findConnectedPoint},
   findConnectedPoint[v : neckl[vList_List]] := (
     Map[Position[First /@ vpList, -#, {3}] &, vList]
         // Map@First
        // Map[{First@#(*,2*)} &]
       // Map[Extract[vpList, #] &]
      // Map@
       Function[{viRule}, 
        If[SameQ[v, First@viRule], Nothing, Last@viRule]]
     );
   Select[vpList, MatchQ[neckl[{a_, b__}] -> _]]
      // Map[Reverse]
     // MapAt[findConnectedPoint, {;; , 2}]
    // Map[evenOrderedSegmentsQ]
   ]
  )

(* doesn't really make sense for even number of legs *)
evenOrderedSegmentsQ[centerPt_Point -> edgePts : {__Point}] := 
 evenOrderedSegmentsQ[First@centerPt -> First /@ edgePts]
evenOrderedSegmentsQ[centerPt_List -> edgePts : {__List}] /; 
  OddQ@Length@edgePts := (
  ArcTan @@ (# - centerPt) & /@ edgePts // N
      // Function[list, (First@list - #) & /@ Rest@list]
     // Mod[#, 2 \[Pi]] &
    // Ordering
   // Signature@# == 1 &
  )

roughGraphPlot[ g_vertexFormGraph ] :=
	Labeled@@@graphPlotForm[g] // Graph

moveGraphVertices[graph_vertexFormGraph] :=
 DynamicModule[{plot, coords, verts, pts0, pts},
  plot = doOrderedPlotUnhighlighted[graph, Sort@getExtLegs@graph];
  coords = 
   getVertexPointsFromOrderedPlot[plot] 
	   //Sow[#,"debug"]&
       //Values // Association // Map@First
	   ;
  verts = Keys@coords;
  pts = pts0 = Values@coords;
  Framed[
   Column[{
     Button["Reset to defaults", (pts = pts0) &],
     LocatorPane[
      Dynamic[pts],
      Dynamic@
       Show[doReorderedPlot[graph, Thread[verts -> pts]]
	   		// highlightUnorderedVertices , 
        ImageSize -> 400],
      Appearance -> Automatic
      ]
     }]
   ]
  ]

End[]

EndPackage[]


