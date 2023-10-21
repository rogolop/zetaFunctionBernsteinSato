/*
	Author: Roger Gomez Lopez
	
	Computation of examples of stratifications of the Bernstein-Sato polynomial
	of plane curves, using the residues of the complex zeta function
*/

// ### Basic requirements ###
AttachSpec("./ZetaFunction/ZetaFunction.spec");
AttachSpec("./SingularitiesDim2/IntegralClosureDim2.spec");
//import "./testSemigroup.m" : MonomialCurveOptions, DeformationCurveSpecific;
Z := IntegerRing();
Q := RationalField();



// ### Input ###

// Whether Magma should quit when the calculations are finished
quitWhenFinished   := true;

// Whether to print into a file, and which one
printToFile        := false;
outFileNamePrefix  := "output/out_";
outFileNameSufix   := ".txt";
// Output format: "table", "CSV", "Latex", "none"
printType          := "table";
// Whether to print
printTopologial    := false;
print_betas        := true;
print_f            := true;

// Which set of nus should be used for each rupture divisor
defaultNus         := [true, true];
nuChoices          := [[], []]; // (if not defaultNus)
discardTopologial  := true; // (if defaultNus)

// Choose curve
curve              := "6-9-22_Artal";
// "6-14-43_Artal"; "6-9-22_Artal"; "4-9_example"; "6-14-43_AM"; "5-7"; "4-6-13"; "_betas";

// For "_betas"
_betas_betas       := [8,18,73];
// [6,9,22]; [10,15,36]; [12,16,50,101]; [12,18,39,79]; [6,14,43]; [5,7]; [4,6,13]; [4,10,21]; [8,18,73]; [6,14,43];
chosenEqs_betas    := [1, 1]; // choose option for each equation
parameters_betas   := "[35,36,37,38]"; //"[7]"; //"[32]"; //"[35,36,37,38]"; // "all"; // "[]";
neededParamsVars   := []; // parameter needed at each Hi
interactive_betas  := false;
interactive_eqs    := false;
interactive_params := false;




// Setup output
outFileName := outFileNamePrefix*curve*outFileNameSufix;
if printToFile then
	if (curve ne "_betas") or not(interactive_betas or interactive_eqs or interactive_params) then
		SetOutputFile(outFileName : Overwrite := true);
	end if;
end if;


// Definition of:
//   - R: the base ring
//   - P = R[x,y]
//   - f: a polynomial in P with a singularity at (0,0)
//   - gs: the sequence of polynomials which separate from f at the i-th rupture divisor
case curve:
	when "2_3":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := x^3 - y^2;
		gs := [f];
	when "3-7_testing":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t1> := BaseRing(P);
		f := -x^7 + t1*x^5*y + y^3;
		gs := [f];
	when "5-7": // 5-7 - deform 4
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t_1,t_4,t_6,'t_{11}'> := BaseRing(P);
		f := 1/7*x^7 + 1/5*y^5 - t_1*x^3*y^3-t_4*x^5*y^2-t_6*x^4*y^3-'t_{11}'*x^5*y^3;
		gs := [f];
	when "4-9": // 4-9 - deform 4
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t_1,t_2,t_6,'t_{10}'> := BaseRing(P);
		f := -(x^9/9+y^4/4) + t_1*x^7*y+t_2*x^5*y^2+t_6*x^6*y^2+'t_{10}'*x^7*y^2;
		gs := [f];
	when "6-7": // 6-7 - deform 6
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
		R<u_1,u_2,u_3,u_8,u_9,'u_{15}'> := BaseRing(P);
		f := x^6 + y^7 + u_1*x^2*y^5 + u_2*x^3*y^4 + u_3*x^4*y^3 + u_8*x^3*y^5 + u_9*x^4*y^4 + 'u_{15}'*x^4*y^5;
		gs := [f];
	when "n-m": // n-m - deform ? - Generic curve construction with 1 characteristic exponent  
		n := 3;
		m := 7;
		//n := StringToInteger(n); //m := n+1;
		curve := Sprint(n)*"-"*Sprint(m);
		Deformation := DeformationCurve([n,m]);
		f := Deformation[1];
		PDeformation := Parent(f);
		totalDim := Rank(PDeformation);
		T := totalDim-2;
		if T gt 0 then      
			P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, T), 2);
			R := BaseRing(P);
			tNames := ["t"*Sprint(i) : i in [1..T]];
			AssignNames(~R, tNames);
			ts := [P | R.i : i in [1..T]];
			f := Evaluate(f, ts cat [x,y]);
			gs := [f];
		else
			P<x,y> := LocalPolynomialRing(Q, 2);
			R := BaseRing(P);
			f := Evaluate(f, [x,y]);
			gs := [f];
		end if;
	when "4-6-13":
		R<t_0,t_1> := RationalFunctionField(Q, 3);
		P<x,y> := LocalPolynomialRing(R, 2);
		R<t_0,t_1> := BaseRing(P);
		f := (x^3-y^2)^2 - x^5*y*(t_0+t_1*x);
		gs := [x^3-y^2, f];
	when "4-6-13_moved":
		R<t_0,t_1> := RationalFunctionField(Q, 3);
		P<x,y> := LocalPolynomialRing(R, 2);
		R<t_0,t_1> := BaseRing(P);
		f := (x^3-(y-x)^2)^2 - x^5*(y-x)*(t_0+t_1*x);
		gs := [x^3-(y-x)^2, f];
	when "8-18-73_t_3":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^9-y^4-t*x^3*y^3)^2 - x^16*y;
		gs := [x^9-y^4-t*x^3*y^3, f];
	when "8-18-73_t_1-2-6-10": // deform first divisor as with 1 exponent
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
		R<t_1,t_2,t_6,t_10> := BaseRing(P);
		f := (-(x^9+y^4) + t_1*x^7*y+t_2*x^5*y^2+t_6*x^6*y^2+t_10*x^7*y^2)^2 - x^16*y;
		gs := [-(x^9+y^4) + t_1*x^7*y+t_2*x^5*y^2+t_6*x^6*y^2+t_10*x^7*y^2, f];
	when "8-18-73_full":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 39), 2);
		R<t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38> := BaseRing(P);
		f := (y^4 + t3*x^3*y^3 + t7*x^4*y^3 + t2*x^5*y^2 - x^9 + t11*x^5*y^3 + t6*x^6*y^2 + t1*x^7*y + t15*x^6*y^3 + t10*x^7*y^2 + t5*x^8*y  + t19*x^7*y^3 + t14*x^8*y^2)^2 + (t36*x^3*y^7 + t37*x^4*y^7 + t35*x^5*y^6 + t38*x^5*y^7 - x^16*y) * ( t0 + t9*y + t4*x + t18*y^2 + t13*x*y + t8*x^2 + t22*x*y^2 + t17*x^2*y + t12*x^3 + t25*x^2*y^2 + t21*x^3*y + t16*x^4 + t28*x^3*y^2 + t24*x^4*y + t20*x^5 + t30*x^4*y^2 + t27*x^5*y + t23*x^6 + t32*x^5*y^2 + t29*x^6*y + t26*x^7 + t33*x^6*y^2 + t31*x^7*y + t34*x^7*y^2 )^2;
		gs := [y^4 + t3*x^3*y^3 + t7*x^4*y^3 + t2*x^5*y^2 - x^9 + t11*x^5*y^3 + t6*x^6*y^2 + t1*x^7*y + t15*x^6*y^3 + t10*x^7*y^2 + t5*x^8*y  + t19*x^7*y^3 + t14*x^8*y^2, f];
	when "8-18-73_t_0":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t_0> := BaseRing(P);
		f := (y^4 - x^9)^2 + (- x^16*y) * ( t_0 )^2;
		gs := [y^4 - x^9, f];
	when "4-18-37":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 11), 2);
		R<t_0,t_1,t_2,t_3,t_4,t_5,t_6,t_7,t_8,t_9,t_10> := BaseRing(P);
		f := (y^2 + t_1*x^5*y + t_3*x^6*y - x^9 + t_5*x^7*y)^2 + (t_0 + t_2*x + t_4*x^2 + t_6*x^3 + t_7*x^4 + t_8*x^5 + t_9*x^6 + t_10*x^7)^2 * (- x^14*y);
		gs := [y^2 + t_1*x^5*y + t_3*x^6*y - x^9 + t_5*x^7*y, f];
	when "10-15-36":
		P<x,y> := LocalPolynomialRing(Q, 2);
		R := BaseRing(P);
		f := (x^3-y^2)^5 -x^18;
		gs := [x^3-y^2, f];
	when "9-21-67":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t_1> := BaseRing(P);
		f := (1/t_1*x^7 - 1/t_1*y^3)^3 - x^20*y;
		gs := [1/t_1*x^7 - 1/t_1*y^3, f];
	when "6-14-43":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t_1> := BaseRing(P);
		f := x^14 - 17/53*x^12*y + 324/2809*x^10*y^2 - 2*x^7*y^3 - 36/53*x^5*y^4 + y^6;
		gs := [-x^7 + (-18/53)*x^5*y + y^3, f];
	when "6-14-43_AM":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^3-y^7)^2 + x*y^12 + t*x^2*y^10; // t = 174002425037731477/11477129801212247256
		gs := [x^3-y^7, f];
	when "4-9_example":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := y^4 - x^9 + t*x^5*y^2;
		gs := [f];
	when "6-14-43_Artal":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^3-y^7)^2 + x^4*y^5 + t*x^2*y^10;
		// -23/86 not root for t = -21/1060 (Artal Singular)
		gs := [x^3-y^7, f];
	when "6-9-22_Artal":
		P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 1), 2);
		R<t> := BaseRing(P);
		f := (x^2-y^3)^3 + x^6*y^2 + t*y^8*(x^2-y^3);
		//                   ^   ^ exponentes cambiados (typo Artal supongo)
		// -23/66 not root for t = -7/10 (Artal Singular)
		gs := [x^2-y^3, f];
	when "_betas": // Generic curve construction  
		// INPUT
		if (interactive_betas) then
			print "\nINPUT: Choose curve semigroup";
			print "Examples: [6,14,43]";
			read _betas, "INPUT>";
			error if (_betas eq ""), "Please define a valid curve semigroup";
			_betas := eval _betas;
			error if (ExtendedType(_betas) ne SeqEnum[RngIntElt]), "Please define a valid curve semigroup";
		else
			_betas := _betas_betas;
		end if;
		error if (not IsPlaneCurveSemiGroup(_betas)), "Please define a valid curve semigroup, given input is not a plane curve semigroup";
		
		// Name
		curve := &*[Sprint(_b)*"-" : _b in _betas];
		curve := curve[1..#curve-1];
		outFileName := outFileNamePrefix*curve*outFileNameSufix;
		if printToFile then
			SetOutputFile(outFileName : Overwrite := true);
		end if;
		
		if (print_betas) then print "Semigroup:", _betas; end if;

		// Topological information
		semiGroupInfo := SemiGroupInfo(_betas);
		g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
		
		// Choice of monomial curve equations and their deformations
		eqs := allMonomialCurves(_betas); // [ [i-th equation options] ]
		if (print_betas) then
			print "Possible undeformed equations in space:";
			for i in [1..#_betas-1] do
				printf "Equation %o options:\n", i;
				print eqs[i];
			end for;
		end if;
		// INPUT
		chosenEqs := [];
		if (interactive_eqs) then
			print "\nINPUT: equation indexes";
			print "Examples: [1,1]";
			read chosenEqs, "INPUT>";
			error if (chosenEqs eq ""), "Please define a valid list of equation indexes";
			chosenEqs := eval chosenEqs;
		else
			chosenEqs := chosenEqs_betas;
		end if;
		error if (ExtendedType(chosenEqs) ne SeqEnum[RngIntElt]), "Please define a valid list of equation indexes";
		error if (#chosenEqs ne (#_betas-1)), "Please define a valid list of equation indexes, wrong # of indexes";
		error if (&or[ (eqIdx le 0) or (eqIdx gt #(eqs[i])) : i -> eqIdx in chosenEqs ]), "Please define a valid list of equation indexes, index out of bounds";
		monomialCurve := [eqs[i, chosenEqs[i]] : i in [1..#_betas-1]]; // Select the chosen equations
		if (print_betas) then print "Chosen equation indexes:", chosenEqs; end if;
		if (print_betas) then print "Chosen equations:"; end if;
		if (print_betas) then print monomialCurve; end if;

		// Deform the chosen monomial curve equations
		Deformation := DeformationCurveSpecific(monomialCurve, _betas);
		
		PDeformation := Universe(Deformation); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] (localization)
		totalDim := Rank(PDeformation);
		g := #Deformation; // g = # of equations in space (H_1, ..., H_g), g+1 = # variables (u_0, ..., u_g)
		T := totalDim-(g+1); // # of parameters (t_0, ..., t_{T-1})
		
		// Restrict deformation such that it can be turned explicitly to plane curve (see TFG-Roger, p.21)
		completeDeformation := true;
		for i in [1..g-1] do
			Hi := Deformation[i];
			// Find and save disallowed terms
			termsToRemove := PDeformation!0;
			for term in Terms(Hi) do
				if &+( Exponents(term)[(T+i+2 +1)..(T+g +1)] ) gt 0 then // u_{i+2}, ..., u_g not allowed in Hi (see TFG-Roger, p.21)
					termsToRemove +:= term;
				elif Exponents(term)[T+i+1 +1] gt 1 then // Allowed degree of u_{i+1} in Hi at most 1 (see TFG-Roger, p.21)
					termsToRemove +:= term;
				end if;
			end for;
			// Remove disallowed terms
			Deformation[i] -:= termsToRemove;
			// Store whether any terms have been removed (in total)
			if termsToRemove ne 0 then
				completeDeformation := false;
			end if;
		end for;
		if (print_betas) then
			print "Can use complete deformation:", completeDeformation;
			print "Usable deformation:";
			print Deformation;
		end if;
		
		// Determine, separate and show the needed and optional deformation parameters
		if (print_betas) then print "Parameters:"; end if;
		neededParams := []; // parameter needed at each Hi
		optionalParams := []; // [ [optional parameters for Hi] ]
		ones := [1 : j in [0..g]]; // [1, ..., 1] corresponding to (u_0, ..., u_g)
		// Parameters of H_1, ..., H_{g-1}
		// H_i = h_i(u_0,...,u_i) - t_?*u_{i+1} + sum_r( t_?*phi_{r,i}(u_0,...,u_g) )
		for i in [1..g-1] do
			Hi := Deformation[i];
			ei := [ (j eq i+1) select 1 else 0 : j in [0..g] ]; // [0, ..., 0, 1, 0, ..., 0] at position corresponding to u_{i+1} among "u"s
			optionalParams[i] := [];
			for term in Terms(Hi) do
				exps := Exponents(term); // exponents of ts and us
				tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
				uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
				if uExps eq ei then // Term t_?*u_{i+1} is necesaryly nonzero, save t_? as needed parameter
					tIndex := Explode([j : j in [0..T-1] | tExps[j+1] gt 0]); // index of t_?
					Append(~neededParams, tIndex);
				else // Term is optional, save the new optional parameters of this divisor
					for j in [0..T-1] do
						if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
							Append(~optionalParams[i], j);
						end if;
					end for;
				end if;
			end for;
			Sort(~optionalParams[i]);
			if (print_betas) then printf "    Optional at E%o: %o\n", i, optionalParams[i]; end if;
		end for;
		// H_g treated separately, no neededParams
		// H_g = h_g(u_0,...,u_g) + sum_r( t_?*phi_{r,g}(u_0,...,u_g) )
		Hg := Deformation[g];
		optionalParams[g] := [];
		for term in Terms(Hg) do
			exps := Exponents(term); // exponents of ts and us
			tExps := exps[1..T]; // exponents of (t_0, ..., t_{T-1})
			uExps := exps[T+1..T+g+1]; // exponents of (u_0, ..., u_g)
			// Term is optional, save the new optional parameters of this divisor
			for j in [0..T-1] do
				if (tExps[j+1] gt 0) and (j notin neededParams) and (j notin &cat(optionalParams)) then
					Append(~optionalParams[g], j);
				end if;
			end for;
		end for;
		Sort(~optionalParams[g]);
		if (print_betas) then
			printf "    Optional at E%o: %o\n", g, optionalParams[g];
			for i in [1..g-1] do
				printf "    Needed at E%o: %o\n", i, neededParams[i];
			end for;
		end if;
		optionalParams := &cat(optionalParams); // optional parameters from any divisor -> [optional parameters]
		
		// Choose deformation parameters
		// INPUT
		if (interactive_params) then
			print "\nINPUT: Choose optional parameters";
			print "Examples: [1,2,3]";
			print "          all";
			read parameters, "INPUT>";
		else
			parameters := parameters_betas;
		end if;
		if parameters eq "all" then
			parameters := optionalParams;
		else
			error if (parameters eq ""), "Please define a valid list of parameters, empty input";
			parameters := eval parameters;
			error if ((ExtendedType(parameters) ne SeqEnum[RngIntElt]) and (parameters ne [])), "Please define a valid list of parameters, given not a sequence of integers";
			for p in parameters do
				error if ((p notin optionalParams) and (p notin neededParams)), "Please define a valid list of parameters, given invalid parameter";
			end for;
		end if;
		parameters cat:= neededParams; // neededParams always have to be included
		parameters := [p : p in Set(parameters)]; // remove duplicates
		Sort(~parameters);
		if (print_betas) then printf "Chosen parameters: %o\n", parameters; end if;
		// Create structures with the new number of parameters
		newT := #parameters; // (temp variable) updated # of parameters (t_0, ..., t_{newT-1})
		PDeformation := LocalPolynomialRing(Q, newT+(g+1)); // polynomial ring with updated # of parameters
		// Create vector "oldToNewParam" which for each old parameter contains the corresponding new parameter (as variable) or a 0
		
		oldToNewParam := [PDeformation| 0 : i in [1..T]];
		k := 1;
		for i in [0..T-1] do
			if (i in parameters) then
				oldToNewParam[i+1] := PDeformation.k; // t_i -> new k-th variable
				k +:= 1;
			end if;
		end for;
		// Update variables
		newUs := [ PDeformation.i : i in [newT+1..newT+(g+1)]]; // new u_0, ..., u_g
		Deformation := [Evaluate(pol, oldToNewParam cat newUs) : pol in Deformation]; // Update variables of Deformation
		T := newT; // Update # of parameters
		delete newT; // (delete temp variable)
		totalDim := T + g+1; // Update total dimension
		// Set parameter and variable names
		if (printType eq "Latex") then
			tNames := ["t_{"*Sprint(i)*"}" : i in parameters ];
			uNames := ["u_{"*Sprint(i)*"}" : i in [0..g] ];
		else
			tNames := ["t"*Sprint(i) : i in parameters ];
			uNames := ["u"*Sprint(i) : i in [0..g] ];
		end if;
		AssignNames(~PDeformation, tNames cat uNames);
		if (print_betas) then
			print "Chosen deformation:";
			print Deformation;
		end if;
		
		// Switch to rational fraction field
		PDefNoLocal := PolynomialRing(BaseRing(PDeformation), totalDim); // Q[t_0, ..., t_{T-1}, u_0, ..., u_g] but non-localized to enable division/fractions
		FP := FieldOfFractions(PDefNoLocal); // Q(t_0, ..., t_{T-1}, u_0, ..., u_g)
		ChangeUniverse(~Deformation, FP);
		
		// Elimination of the variables u_2, ..., u_g
		// Invariant property (as ensured before): u_{i+2}, ..., u_g not in Hi, u_{i+1} with exponent at most 1 in Hi
		gs := [FP| ]; // Parts of the equations Hi, relevant later for their proximity to the curve f
		for i in [1..g-1] do
			Hi := Numerator(Deformation[i]); // We are interested in Hi=0 -> denominators don't matter
			u_ip1 := PDefNoLocal.(T+1+ i+1); // u_{i+1} as polynomial
			// Define: Hi = gs[i] + u_{i+1}*uDenom
			gs[i]  := Coefficient(Hi, u_ip1, 0);
			uDenom := Coefficient(Hi, u_ip1, 1);
			// Solve for u_{i+1}:
			// Hi = gs[i] + u_{i+1}*uDenom = 0 <=> u_{i+1} = - gs[i] / uDenom
			u_ip1_value := - gs[i] / uDenom; // function of (u_0, u_1) because of the invariant property and the elimination of (u_2, ..., u_i) in previous iterations
			// Substitute value of u_{i+1} in the remaining equations, thus eliminating u_{i+1}
			// As the value of u_{i+1} is a function of (u_0, u_1), the invariant property is preserved
			for j in [i+1..g] do
				Deformation[j] := Evaluate(Deformation[j], (T+1+ i+1), u_ip1_value); // Substitute value of u_{i+1}
				Deformation[j] := Numerator(Deformation[j]); // Remove denominators
			end for;
		end for;
		f := Deformation[g]; // Resulting plane curve equation
		gs[g] := f;
		// Switch back to polynomial ring (no denominators)
		ChangeUniverse(~gs, PDefNoLocal);
		f := PDefNoLocal ! f;
		
		// Separate parameters into the coefficient ring
		// From: Q[t_0, ..., t_{T-1}, u_0, ..., u_g]
		// To:   Q(t_0, ..., t_{T-1})[x,y]
		// u_0=x, u_1=y, ( u_2, ..., u_g have already been eliminated from the polynomials, can be evaluated to 0 )
		if T eq 0 then
			P<x,y> := LocalPolynomialRing(Q, 2);
			R := BaseRing(P);
			ts := [P | ];
		else
			P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, T), 2);
			R := BaseRing(P);
			if (printType eq "Latex") then
				tNames := ["t_{"*Sprint(i)*"}" : i in parameters ];
			else
				tNames := ["t"*Sprint(i) : i in parameters ]; // in [1..T]
			end if;
			AssignNames(~R, tNames);
			ts := [P | R.i : i in [1..T]];
		end if;
		gs := [Evaluate(pol, ts cat [x,y] cat [0 : i in [2..g]]) : pol in gs];
		//gUnits := [Evaluate(pol, ts cat [x,y] cat [0 : i in [2..g]]) : pol in gUnits];
		f := Evaluate(f, ts cat [x,y] cat [0 : i in [2..g]]);
		
		// Save needed non-zero parameters as variables
		for i in neededParams do
			j := Position(parameters, i);
			Append(~neededParamsVars, R.j);
		end for;
		
	else: // input error
		error "Please define a valid f";
end case;

// ### To do before starting ###

if (printType eq "CSV") then
	printf "\nCurve, %o\n", curve;
	if print_f then printf "f, %o\n\n", f; end if;
elif (printType eq "table") then
	printf "\nCurve: %o\n\n", curve;
	if print_f then printf "f = %o\n\n", f; end if;
elif (printType eq "Latex") then
	printf "\nCurve: %o\n\n", curve;
	if print_f then printf "f = %o\n\n", f; end if;
end if;


// Flush to file
if printToFile then
	UnsetOutputFile();
	SetOutputFile(outFileName : Overwrite := false);
end if;


// ### Algebraic information ###

// Multiplicities
Nps, kps, Ns, ks := MultiplicitiesAtAllRuptureDivisors(f);
// Semigroup
_betas := SemiGroup(f); // minimal set of generators of the semigroup
semiGroupInfo := SemiGroupInfo(_betas);
g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
// Variables in the for-loop
n, q, Np, kp, N, k, nus, L_all, sigma_all, epsilon_all := Explode(["not yet assigned" : i in [1..100]]);

topologicalRoots := []; // [ [topological roots of divisor r] ]
ignoreDivisor := [ (not defaultNus[i]) and (nuChoices[i] eq []) : i in [1..g] ]; // ignore the divisor if no "nus" should be checked


// Find duplicate root candidates (-> monodromy has repeated eigenvalues)
allSigmas := {Q| };
sigmaToIndexing := AssociativeArray();
for r in [1..g] do
	Np, kp, N, k := MultiplicitiesAtThisRuptureDivisor(r, Nps, kps, Ns, ks);
	nus, topologicalNus := Nus(_betas, semiGroupInfo, Np, kp, r : discardTopologial:=false);
	for nu in nus do
		sigma := Sigma(Np, kp, nu);
		if sigma in allSigmas then
			R, NU := Explode(sigmaToIndexing[sigma]);
			printf "WARNING! Candidates coincide: sigma_{%1o,%3o} = sigma_{%1o,%3o} = %-8o \n", R, NU, r, nu, sigma;
		else
			Include(~allSigmas, sigma);
			sigmaToIndexing[sigma] := <r, nu>;
		end if;
	end for;
end for;
printf "\n";



strictTransform_f := f;
xyExp_f := [0,0];
xyExp_w := [0,0];
units_f := {* P!1 *};
units_w := {* P!1 *};
pointType := 0; // 0 -> basepoint, 1 -> free point, 2 -> satellite point
PI_TOTAL := [x, y];

// ### For each rupture divisor ###
// Non-rupture divisors don't have to be ckecked (see TFG-Roger, p.28, Cor.4.2.5)
for r in [1..g] do
	print "-----------------------------------------------------------------------";
	if (printType ne "none" and not ignoreDivisor[r]) then printf "Divisor E_%o\n", r; end if;
	
	// Blowup
	// From: (0,0) singular point of the strict transform of the curve (basepoint or a free point on last rupture divisor)
	// To: next rupture divisor
	strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType, lambda, ep, PI_blowup := Blowup(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType);
	// Total blowup morphism since basepoint
	PI_TOTAL := [Evaluate(t, PI_blowup) : t in PI_TOTAL];
	// Units
	U := &*[t^m : t->m in units_f] * strictTransform_f;
	V := &*[t^m : t->m in units_w];
	// Multiplicities of rupture divisor x=0
	NP := xyExp_f[1];
	KP := xyExp_w[1];
	// Multiplicities of y=0
	N1 := xyExp_f[2];
	K1 := xyExp_w[2];
	// Multiplicities of:
	// 1) proximate non-rupture divisor through (0,0): y=0
	// 2) proximate non-rupture divisor through (0,infinity)
	// 3) the curve
	NN := [N1, NP-N1-ep, ep];
	KK := [K1, KP-K1-1, 0];
	
	// // Find the maximum nu in this and following rupture divisors => maximum power needed in series expansions in x (?????????)
	// // Don't discard topological roots to have enough terms for a blowup
	// M := 0;
	// for i in [r..g] do
	// 	Npi, kpi, Ni, ki := MultiplicitiesAtThisRuptureDivisor(i, Nps, kps, Ns, ks);
	// 	M := Max( [M] cat Nus(_betas, semiGroupInfo, Npi, kpi, i : discardTopologial:=false) );
	// end for;
	
	// Interesting values of nu
	nus, topologicalNus := Nus(_betas, semiGroupInfo, NP, KP, r : discardTopologial:=discardTopologial);
	topologicalRoots[r] := [<nu, Sigma(NP, KP, nu)> : nu in topologicalNus];
	if not defaultNus[r] then
		nus := nuChoices[r];
	end if;
	// Print...
	if not ignoreDivisor[r] then
		if (printType eq "CSV") then
			printf "nus, ";
			for i->nu in nus do
				printf "%o", nu;
				if (i lt #nus) then printf ", "; end if;
			end for;
			printf "\n\n";
		elif (printType in {"table","Latex"}) then
			printf "nus = %o\n\n", nus;
		end if;
	end if;
	
	print "-----------------------------------------------------------------------";
	print "ZetaFunctionResidue";
	
	// Flush to file
	if printToFile then
		UnsetOutputFile();
		SetOutputFile(outFileName : Overwrite := false);
	end if;
	
	L_all, sigma_all, epsilon_all := ZetaFunctionResidue(< P, [x,y], PI_TOTAL[1], PI_TOTAL[2], U, V, lambda, ep, NP, KP, NN, KK, nus, r, neededParamsVars, printToFile, outFileName> : printType:=printType);
	
	// Flush to file
	if printToFile then
		UnsetOutputFile();
		SetOutputFile(outFileName : Overwrite := false);
	end if;
	
	// Prepare next iteration
	if r lt g then
		print 	"-----------------------------------------------------------------------";
		print "Center singular point";
		
		strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, PI_center := CenterOriginOnCurve(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, lambda);
		// Total blowup morphism since basepoint
		PI_TOTAL := [Evaluate(t, PI_center) : t in PI_TOTAL];
		
		printf "lambda = %o\n\n", lambda;
	end if;
end for;



if (printType ne "none" and printTopologial) then
	if printType eq "table" then
		for r in [1..g] do
			if not ignoreDivisor[r] then
				printf "Topological roots at divisor E_%o\n", r; 
				printf " nu  │         sigma\n";
				printf "─"^5*"┼";
				printf "─"^22*"\n";
				for tup in topologicalRoots[r] do
					nu, sigma := Explode(tup);
					Np := Nps[r];
					printf "%4o │ %4o/%-4o = %8o\n", nu, (sigma*Np), Np, sigma;
				end for;
				printf "\n";
			end if;
		end for;
	elif printType eq "Latex" then
		for r in [1..g] do
			if not ignoreDivisor[r] then
				printf "Topological roots at divisor E_%o\n", r; 
				printf "        $\\nu$&$\\sigma_{%o,\\nu}$\\\\", r;
				printf "\\hline\\hline\n";
				for tup in topologicalRoots[r] do
					nu, sigma := Explode(tup);
					Np := Nps[r];
					//printf "-\\frac{%o}{%o}, ", Numerator(-sigma), Denominator(sigma);
					printf "        $%4o $&$ %4o/%-4o =  %8o $\\\\\n", nu, (sigma*Np), Np, sigma;
				end for;
				printf "\n\n";
			end if;
		end for;
	end if;
end if;

// ### To do when finished ###

if printToFile then
	UnsetOutputFile();
	printf "Printed to: %o\n", outFileName;
end if;

if quitWhenFinished then
	quit;
end if;
