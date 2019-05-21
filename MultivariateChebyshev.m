(* Wolfram Language Package *)

(* Created by the Wolfram Workbench 28.12.2016 *)

BeginPackage["MultivariateChebyshev`"]
(* Exported symbols added here with SymbolName::usage *) 


WeylGroup::usage = 
    "WeylGroup[roots] returns the Weyl group associated to the roots given 
	in homogeneous coordinates. The Weyl group is returned in standard 
	coordinates and transposed form."
   
Chebyshev::usage = 
    "Chebyshev[t,n,W,rep,admissible] returns the nth Chebyshev Polynomial in 
	trigonometric coordinates associated to the root system defined
	by the Weyl group W with representation rep and minimal admissible sets admissible."
	
ChebyshevGeneratingFunction::usage = 
	"ChebyshevGeneratingFunction[p,t,W,rep,admissible] returns the generating function for  Chebyshev polynomials of rep type"
    
ChebyshevToPowerForm::usage =
    "ChebyshevToPowerForm[p,t,u] gives the Power-Form of the Chebyshev polynomial
	p, t being the angle coordinates and u the corresponding power bases" 
    
ChebyshevRecurrenceRelationLatex::usage =
    "ChebyshevRecurrenceRelation[k,l,type] gives the recurrence relation for Chebyshev
		polynomials of type in Latex Code"
    
ChebyshevRecurrenceRelationRightHandSideIndices::usage =
    "Gives the right hand side of the recurrence relation for indices k,l and type"
    
HouseholderMatrix::usage =
    "Returns a the HouseholderMatrix of vec"
    
SimpleRoots::usage =
    "Returns a set of simple roots of type"
    
WeylGroupOrbit::usage =
    "Returns the WeylGroupOrbit of an element of the index space"

Begin["`Private`"]
(* Implementation of the package *)


Chebyshev[t_,n_, roots_] :=
    Block[ {W},
        W = WeylGroup[roots];
        Chebyshev[t,n,W]
    ]

Chebyshev[t_,n_, type_?StringQ] :=
    Block[ {W},
        W = WeylGroup[type];
        Chebyshev[t,n,W]
    ]
    
Chebyshev[t_,n_,W_] :=
    Block[ {T,i},
        T = 1/Length[W]*Sum[Exp[2*Pi*I*(n.Transpose[W[[i]]].t)], {i, Length[W]}]
    ]
    
Chebyshev[t_,n_,W_,rep_,admissible_] :=
    Block[ {T,i,a,minimalFunction,nominator},
    	(*Calculate MinimalFunction *)
        minimalFunction = 1/ Length[W] Simplify[Sum[ Sum[rep[W[[i]]]  Exp[2*Pi*I*((a).Transpose[W[[i]]].(t))], {i, Length[W]}], {a,admissible}]];
        nominator = 1/ Length[W] Simplify[Sum[rep[W[[i]]]  Exp[2*Pi*I*((n).Transpose[W[[i]]].(t))], {i, Length[W]}]];
        T = Simplify[ 1/(minimalFunction)  * nominator]
    ] /; Length[rep @ W[[1]]] == 0
    
Chebyshev[t_,n_,W_,rep_,admissible_] :=
    Block[ {T,i,a,minimalFunction,nominator},
    	(*Calculate MinimalFunction *)
        minimalFunction = 1/ Length[W] Simplify[Sum[ Sum[rep[W[[i]]]  Exp[2*Pi*I*((a).Transpose[W[[i]]].(t))], {i, Length[W]}], {a,admissible}]];
        nominator = 1/ Length[W] Simplify[Sum[rep[W[[i]]]  Exp[2*Pi*I*((n).Transpose[W[[i]]].(t))], {i, Length[W]}]];
        T = Simplify[ Inverse[minimalFunction].nominator ]
    ]
    
ChebyshevGeneratingFunction[p_,t_, W_, rep_, admissible_] :=
	Block[ {minimalFunction,matrixGenFunNominator,a,i},
		minimalFunction =  1/Length[W] Simplify[ Sum[Sum[rep[W[[i]]] Exp[2*Pi*I*((a).Transpose[W[[i]]].(t))], {i, Length[W]}], {a, admissible}]];
		matrixGenFunNominator = Total[Times[rep /@ W, Product[1/(1 - p[[i]] Exp[2 Pi I #[[i]]]), {i,Length[p]}]&  /@  WeylGroupOrbit[(t), Transpose /@ W]]];
     1/minimalFunction  * matrixGenFunNominator
    ]/; Length[rep @ W[[1]]] == 0
    
ChebyshevGeneratingFunction[p_,t_, W_, rep_, admissible_] :=
	Block[ {minimalFunction,matrixGenFunNominator,a,i},
		minimalFunction =  1/Length[W] Simplify[ Sum[Sum[rep[W[[i]]] Exp[2*Pi*I*((a).Transpose[W[[i]]].(t))], {i, Length[W]}], {a, admissible}]];
		matrixGenFunNominator = Total[Times[rep /@ W, Product[1/(1 - p[[i]] Exp[2 Pi I #[[i]]]), {i,Length[p]}]&  /@  WeylGroupOrbit[(t), Transpose /@ W]]];
     Inverse[minimalFunction].matrixGenFunNominator
    ]
   
ChebyshevToPowerForm[p_, t_, u_] := 
 Block[{expT, i, tmpp}, tmpp = p /. Power[E, a_] :> expT@Expand@a;
  tmpp = tmpp //. {expT[a_ + b_] :> expT[a] expT[b]};
  tmpp = tmpp /. {expT[a_] :> expT[a/(2 Pi I)]};
  tmpp //. {Flatten[
     Table[{expT[a_ t[[i]]] -> u[[i]]^a, expT[t[[i]]] -> u[[i]]}, {i, 
       Length[t]}]]}
       ]
  
    
ChebyshevRecurrenceRelationLatex[k_, l_, type_?StringQ] :=
    Block[ {i,W,tmp, ind},
        W = WeylGroup[type];
        ind = ChebyshevRecurrenceRelationRightHandSideIndices[k,l,W];
        tmp = "T_{" <> ToString[k] <> "} \\cdot T_{" <> ToString[l] <>"}";
        tmp = tmp <> " =  \\frac{1}{" <> ToString[Length[W]] <> "} \\left( " <> ToString[Sum[ToString[ind[[i,1]]] <>"T_{" <> ToString[ind[[i,2]]] <> "} ", {i,Length[ind]}]] <> " \\right)";
        tmp
    ]
    
    
Options[ChebyshevRecurrenceRelationRightHandSideIndices] = {Assuming -> $Assumptions}
    
ChebyshevRecurrenceRelationRightHandSideIndices[k_, l_, type_?StringQ,OptionsPattern[]] :=
    Block[ {},
        ChebyshevRecurrenceRelationRightHandSideIndices[k,l,WeylGroup[type], OptionsValue[Assuming]]
    ]
    
ChebyshevRecurrenceRelationRightHandSideIndices[k_, l_, W_,OptionsPattern[]] :=
    Block[ {i,tmp, lengths},
        tmp = Table[
            Assuming[Assumptions,
                PositivizeIndices[k+W[[i]].l,W]
                ],
             {i, Length[W]}];
        lengths =  Length /@ GatherBy[tmp, Sort[WeylGroupOrbit[#1, W]] &];
        tmp = DeleteDuplicatesBy[tmp, Sort[WeylGroupOrbit[#1, W]] &];
        Table[{lengths[[i]]/Length[W], tmp[[i]]}, {i, Length[tmp]}]
    ]
    
  
SimpleRoots[type_?StringQ] :=
    Block[ {roots, family, dim},
        family = Characters[type][[1]];
        dim = ToExpression[StringJoin[Characters[type][[2;;]]]];
        Switch[family,            
            "A", roots = Table[UnitVector[dim+1,i]-UnitVector[dim+1,i+1], {i,dim}],
            "B", roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]}],
            "C", roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {2*UnitVector[dim,dim]}],
            "D", roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]+UnitVector[dim,dim-1]}],
            "G", roots = {{1,-1,0},{-1,2,-1}},
            _, "Not yet implemented!"
        ];
        (* Project the roots in their least dimensional space *)
        DeleteCases[Orthogonalize[roots], ConstantArray[0, Length[roots[[1]]]]].Transpose[roots] // Transpose
    ]

WeylGroupOrbit[k_, type_?StringQ] :=
    Block[ {i,W},
        W = WeylGroup[type];
        Table[W[[i]].k, {i, Length[W]}]
    ]


WeylGroupOrbit[k_, W_] :=
    Block[ {i},
        Table[W[[i]].k, {i, Length[W]}]
    ]

    
    
WeylGroup[type_?StringQ] :=
    Block[ {roots, family, dim},
        family = Characters[type][[1]];
        dim = ToExpression[StringJoin[Characters[type][[2;;]]]];
        Switch[family,            
            "A", (roots = Table[UnitVector[dim+1,i]-UnitVector[dim+1,i+1], {i,dim}];
                  WeylGroup[roots] ),
            "B", (roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]}];
                  WeylGroup[roots]),
            "C", (roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {2*UnitVector[dim,dim]}];
                  WeylGroup[roots]),
            "D", (roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]+UnitVector[dim,dim-1]}];
                  WeylGroup[roots]),
            "G", (roots = {{1,-1,0},{-1,2,-1}};
                  WeylGroup[roots] ),
            _, "Not yet implemented!"
        ]
    ]

WeylGroup[roots_] :=
    Block[ {proj, gens,matrices},
        (* Project the roots in their least dimensional space *)
        proj = DeleteCases[Orthogonalize[roots], ConstantArray[0, Length[roots[[1]]]]].Transpose[roots] // Transpose; 
        (* Calculate the generators of the Weyl group *)
        gens = HouseholderMatrix /@ proj;    
        (* Base Change to Basis consisting of roots *)
        gens = Simplify[(proj.#1.Inverse[proj])] & /@ gens; 
        (* generate the group via brute force*)
        FixedPoint[Union[#, Dot @@@ Tuples[#, 2]] &, gens]
    ]
    
HouseholderMatrix[v_?VectorQ] :=
    Module[ {},
        IdentityMatrix[Length[v]] - 2 Transpose[{v}] . {v} / (v.v)
    ]    
End[]

EndPackage[]

