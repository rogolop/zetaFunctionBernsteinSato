/*
	Author: Roger Gomez Lopez
	
	Formal derivatives, residues of the complex zeta function, helping functions for the changes of variable
*/

// Formal derivatives

intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], xi::RngMPolLocElt) -> SeqEnum, SetEnum
	{
		Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to xi.
		
		F       : sequence of sequences m times, where F[a1,...,am] represents the
							coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...).
		indexsF : nonzero elements of F.
		g       : sequence of functions [g1,...,gm] of (x1,...).
		xi      : derive with respect to xi.
	}
	m := #g;
	DiF := [];
	indexsDiF := indexsF;
	
	// Derivate
	for a in indexsF do
		value := Derivative(SeqElt(F,a),1,xi);
		AssignSeqElt(~DiF, a, value);
	end for;
	
	for a in indexsF do
		for L in [1 .. m] do
			b := a;
			b[L] +:= 1;
			value := SeqElt(F,a) * Derivative(g[L],1,xi);
			PlusAssignSeqElt(~DiF, b, value);
			Include(~indexsDiF, b);
		end for;
	end for;
	
	// Remove zeros
	for a in indexsDiF do
		if SeqElt(DiF,a) eq 0 then
			UndefineSeqElt(~DiF, a);
			Exclude(~indexsDiF, a);
		end if;
	end for;
	
	return DiF, indexsDiF;
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], i::RngIntElt) -> SeqEnum, SetEnum
	{
		Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to xi.
		
		F       : sequence of sequences m times, where F[a1,...,am] represents the
							coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...).
		indexsF : nonzero elements of F.
		g       : sequence of functions [g1,...,gm] of (x1,...).
		i       : derive with respect to the i-th variable.
	}
	return FormalDerivative(F, indexsF, g, Universe(g).i);
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, xi::RngMPolLocElt) -> SeqEnum, SetEnum
	{
		Derivative of (F o g), k times with respect to xi
	}
	for j in [1..k] do
		F, indexsF := FormalDerivative(F, indexsF, g, xi);
	end for;
	return F, indexsF;
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, i::RngIntElt) -> SeqEnum, SetEnum
	{
		Derivative of (F o g), k times with respect to the i-th variable
	}
	return FormalDerivative(F, indexsF, g, k, Universe(g).i);
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], L::SeqEnum[Tup]) -> SeqEnum, SetEnum
	{
		L = Set( <k_1,i_1>, ..., <k_n,i_n> )
			or
		L = Set( <k_1,x_i_1>, ..., <k_n,x_i_n> ).
		Derivate of (F o g) with respect to x_i, k times, for all <k,x_i> in L
	}
	if #L gt 0 then
		k, v := Explode(L[1]);
		require Type(k) eq RngIntElt and (Type(v) eq RngMPolLocElt or Type(v) eq RngIntElt) : "Bad argument types inside tuples of L\nArgument types given:", Type(k), ",", Type(v);
	end if;
	
	for t in L do
		k, v := Explode(t);
		F, indexsF := FormalDerivative(F, indexsF, g, k, v);
	end for;
	return F, indexsF;
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, xi::RngMPolLocElt, discard::SeqEnum) -> SeqEnum, SetEnum
	{
		Derivative of (F o g), k times with respect to xi.
		Discard terms with powers higher than x_discardVar^discardPow at the result
	}
	discardVar, discardPow := Explode(discard);
	Z := IntegerRing();
	if #indexsF gt 0 then
		P := Parent(SeqElt(F,Rep(indexsF)));
	end if;
	
	// Truncate polynomials at x_discardVar^m where m is too high
	for I in indexsF do
		AssignSeqElt(~F, I,  &+[P | t : t in Terms(SeqElt(F,I)) | Degree(t,discardVar) le (k+discardPow)]);
	end for;
	
	// Derivate k times, truncating high powers
	for j in [1..k] do
		// Derivate once
		F, indexsF := FormalDerivative(F, indexsF, g, xi);
		// Truncate polynomials at x_discardVar^m where m is too high
		for I in indexsF do
			AssignSeqElt(~F, I,  &+[P | t : t in Terms(SeqElt(F,I)) | Degree(t,discardVar) le (k-j+discardPow)]);
		end for;
	end for;
	
	return F, indexsF;
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, i::RngIntElt, discard::SeqEnum) -> SeqEnum, SetEnum
	{
		Derivative of (F o g), k times with respect to the i-th variable.
		Discard polynomials that will result in x_discardVar^discardPow*(...) at the result
	}
	return FormalDerivativeDiscardingVar(F, indexsF, g, k, Universe(g).i, discard);
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], L::SeqEnum[Tup], discard::SeqEnum) -> SeqEnum, SetEnum
	{
		L = Set( <k_1,i_1>, ..., <k_n,i_n> )
			or
		L = Set( <k_1,x_i_1>, ..., <k_n,x_i_n> ).
		Derivate of (F o g) with respect to x_i, k times, for all <k,x_i> in L.
		Discard polynomials that will result in x_discardVar^discardPow*(...) at the result
	}
	if #L gt 0 then
		k, v := Explode(L[1]);
		require Type(k) eq RngIntElt and (Type(v) eq RngMPolLocElt or Type(v) eq RngIntElt) : "Bad argument types inside tuples of L\nArgument types given:", Type(k), ",", Type(v);
	end if;
	
	for t in L do
		k, v := Explode(t);
		F, indexsF := FormalDerivativeDiscardingVar(F, indexsF, g, k, v, discard);
	end for;
	return F, indexsF;
end intrinsic;


// Residues

function between0and1(x)
	// return r in the interval (0,1] differing from x in an integer value
	r := x - Floor(x);
	if (r eq 0) then return 1; end if;
	return r;
end function;


function GammaFromTo_Risky(f, t)
	// GammaFromTo(f, t) = Gamma(f) / Gamma(t)
	// Don't avoid zeros and infinities, may cause errors.
	// (f-t) must be integer
	error if ((f-t) notin IntegerRing()), "At GammaFromTo(f, t): f and t must differ by an integer\nGiven arguments:", f, ",", t;
	
	coef := 1;
	
	while (f gt t) do
		f -:= 1;    
		coef *:= f;
	end while;
	
	while (f lt t) do
		coef /:= f;
		f +:= 1;
	end while;
	
	return coef;
end function;


intrinsic E(l::RngIntElt, k::RngIntElt, epsilon::[], ep::RngIntElt) -> FldFunRatMElt
	{
		Gamma(l+epsilon+1) * Gamma(sigma-i+1) / Gamma(l+epsilon+sigma-i+2) * 1/ref, with ref = Gamma(a) * Gamma(b) / Gamma(c), where a,b,c are in the interval (0,1] differing of the first values by integer numbers.
	}
	e := 1;
	
	arg := epsilon[1] + 1 + l;
	e *:= GammaFromTo_Risky(arg, between0and1(arg));
	//e *:= GammaFromTo_Risky(arg, epsilon[1] + 1);
	
	arg := epsilon[3] + 1 - ep*k;
	e *:= GammaFromTo_Risky(arg, between0and1(arg));
	//e *:= GammaFromTo_Risky(arg, epsilon[3] + 1);
	
	arg := epsilon[1] + epsilon[3] + 2 + l - ep*k;
	e /:= GammaFromTo_Risky(arg, between0and1(arg));
	//e /:= GammaFromTo_Risky(arg, epsilon[1] + epsilon[3] + 2 ); 
	return e;
end intrinsic;


intrinsic SeparateYTerms(s::SeqEnum, indexs::SetEnum) -> SeqEnum
	{
		Convert each polynomial in s to a sequence of pairs [l,term], there term is the coefficient of y^l of the polynomial (as member of R[y] with the corresponding ring R)
	}  
	function listYTerms(f)
		L := [];
		for l in [0..Degree(f,2)] do
			term := Coefficient(f, 2, l);
			if term ne 0 then
				Append(~L, <l, term>);
			end if;
		end for;
		return L;
	end function;
	
	w := [];
	for I in indexs do
		AssignSeqElt(~w, I, listYTerms(SeqElt(s, I)));
	end for;
	
	return w;
end intrinsic;


function FallingFactorial(n, k)
	return &*[Parent(n) | (n-i) : i in [0..k-1]];
end function;


intrinsic nonconjugateResidue(DPhi_terms::SeqEnum, indexs_DPhi::SetEnum, sigma::FldRatElt, lambda::FldElt, epsilon::[], ep::RngIntElt) -> SeqEnum, SetEnum
	{
		"Nonconjugate" part of the residue of the complex zeta function, with indexing representing the derivatives of delta(x,y). Multiply the result by its conjugate to obtain the full residue (apart from the multiplying constant).
	}
	Res := [];
	indexs_Res := {};
	
	for ijk in indexs_DPhi do
		ij := ijk[1..2]; // numbers of derivatives of delta distribution (+1: kept as indexs)
		k := ijk[3]-1; // number of derivatives of u^s
		
		// Integrate
		pijk_seq := SeqElt(DPhi_terms, ijk);
		res := 0;
		for pair in pijk_seq do
			l, pijkl := Explode(pair);
			// Add term to the residue
			res +:= pijkl * lambda^(-l) * E(l, k, epsilon, ep);
		end for;
		PlusAssignSeqElt(~Res, ~indexs_Res, ij, res);
	end for;
	
	// Remove zeros
	for ij in indexs_Res do
		if SeqElt(Res, ij) eq 0 then
			Exclude(~indexs_Res, ij);
		end if;
	end for;
	return Res, indexs_Res;
end intrinsic;


intrinsic FactorizedBasis(Res::[], indexs_Res::{}, P::RngMPolLoc, invertibleVariables::[]) -> []
	{
		Get a simplified basis of polynomials, as sequences of factors without multiplicity, without denominators
	}
	R := BaseRing(P);
	Rpol := Parent(Numerator(R!1));
	
	// Ignore which (derivative of) delta-function they multiply. Each polynimial multiplies to a different delta-function, so the residue is only 0 at common roots of all polynomials.
	// Coerce into a nonlocal polynomial ring for the function Reduce()
	listRes := [R | SeqElt(Res, ij) : ij in indexs_Res ];
	
	// If the residue is the constant 0 (listRes is [])
	if #listRes eq 0 then
		return [[R|0]]; // Return the polynomial 0 for clarity
	end if;
	
	if (Type(R) eq FldFunRat) then
		listRes := [Rpol | Numerator(elt) : elt in listRes];
		//RHelpPol := PolynomialRing(PolynomialRing(IntegerRing(), #neededParams), Rank(R)-#neededParams);
		listRes := Reduce(listRes);
		//listRes := EasyBasis( ideal<Rpol | listRes>);
		//listRes := SmallBasis( ideal<Rpol | listRes>);
		//print listRes;
	else
		if (#[R | elt : elt in listRes | IsUnit(elt)] gt 0) then
			listRes := [1];
		end if;
	end if;
	
	// If the residue never vanishes (has a nonzero constant term)
	if listRes in [[1]] then 
		return [[R|1]]; // Return the polynomial 1 for clarity
	end if;
	
	// If the execution arrives here, listRes is a nonempty list of nonconstant polynomials. Then separate the factors and clear coefficient denominators (multiplicative constants don't affect zeros)
	if (Type(R) eq FldFunRat) then
		L := [ [R | ClearDenominators(tup[1]) : tup in Factorization(g)] : g in listRes];
		// print Parent(Factorization(listRes[1])[1][1]);
		// print Parent(invertibleVariables[1]);
		// print Parent(Rpol!invertibleVariables[1]);
		
		/*
		L := [
						[
							R |
							ClearDenominators(tup[1]) : tup in Factorization(g) | // integer coefficients
							&and[Rpol!tup[1] ne Rpol!t : t in invertibleVariables] // ensure polynomial is not = non-zero variable
						] :
						g in listRes
					];
		
		if (&or[#l eq 0 : l in L]) then
			return [[R|1]];
		end if;
		*/
		//L := [ l : l in L | #l gt 0 ]; // remove empty terms []
		
		// If one of the conditions is that a non-zero variable is 0, the residue never vanishes
		for l in L do
			if ((#l eq 1) and &or[Rpol!(l[1]) eq Rpol!R.t : t in invertibleVariables]) then
				return [[R|1]];
			end if;
		end for;
		
		// If one of the conditions is that either a non-zero variable is 0 or something else is 0, then that something else is 0
		// We can remove the condition of the non-zero variable
		for i in [1..#L] do
			l := L[i];
			removedTermsNum := 0;
			for j in [1..#l] do
				pol := l[j];
				if (&or[Rpol!pol eq Rpol!R.t : t in invertibleVariables]) then
					Remove(~(L[i]), j-removedTermsNum);
					removedTermsNum +:= 1;
				end if;
			end for;
		end for;
		
	else
		L := [ [R | g] : g in listRes];
	end if;
	
	//L := [[p]: p in listRes];
	return L;
end intrinsic;


intrinsic SimplifiedBasis(Res::[], indexs_Res::{}, P::RngMPolLoc, invertibleVariables::[]) -> []
	{
		Get a simplified basis of polynomials
	}
	if #indexs_Res eq 0 then return [P| 0]; end if;
	
	// Ignore which derivative of delta-function
	listRes := [P | SeqElt(Res, ij) : ij in Sort([IJ : IJ in indexs_Res]) ];
	
	// Check that the residues have no terms with x,y => residues are in R
	error if (&or[Degree(res) gt 0 : res in listRes]), "At SimplifiedBasis(Res, indexs_Res, P, invertibleVariables): Res contains x or y\nGiven arguments:", Res, ",", indexs_Res, ",", P, ",", invertibleVariables;

	R := BaseRing(P); // P = R[x,y]
	listRes := [R| MonomialCoefficient(res, P!1) : res in listRes]; // residues are equal to the constant term in x,y
	if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
		nonInvertibleVariables := [ i : i in [1..Rank(R)] | i notin invertibleVariables];
		if #invertibleVariables eq 0 then
			Q := BaseRing(R);
			Qnew := Q;
		else
			Q := BaseRing(R);
			// Qnew = Q(t_1,...,t_r)
			Qnew := RationalFunctionField(Q, #invertibleVariables);
			AssignNames(~Qnew, [Sprint(R.i) : i in invertibleVariables]);
		end if;
		// Rnew = Qnew[t_{r+1},...,t_k]
		Rnew := PolynomialRing(Qnew, #nonInvertibleVariables);
		AssignNames(~Rnew, [Sprint(R.i) : i in nonInvertibleVariables]);
		
		newVarsInOldOrder := [Rnew| 0 : i in [1..Rank(R)]];
		for newPos->oldPos in invertibleVariables do
			newVarsInOldOrder[oldPos] := Qnew.newPos;
		end for;
		for newPos->oldPos in nonInvertibleVariables do
			newVarsInOldOrder[oldPos] := Rnew.newPos;
		end for;
		
		listResNew := [Rnew| Evaluate(res, newVarsInOldOrder) : res in listRes];
		// listResNew := [Pnew| ];
		// for res in listRes do
		// 	coefficients, monomials := CoefficientsAndMonomials(res);
		// 	resNew := Pnew!0;
		// 	for i in [1..#monomials] do
		// 		coeff := Evaluate(coefficients[i], newVarsInOldOrder);
		// 		monomial := Evaluate(monomials[i], [0,0]);
		// 		resNew +:= coeff * monomial;
		// 	end for;
		// 	Append(~listResNew, resNew);
		// end for;
		//listResNew := ClearDenominators(listResNew);
		
		listResNew := Reduce(listResNew);
		return listResNew;
		
	// elif ISA(Type(R),Fld) then
	// 	// Can clear denominators (not taking into account invertibleVariables)
	// 	listResNew := Reduce(listRes);
	// 	return listResNew;
	else
		//listResNew := [P| res : res in listRes | not IsUnit(res)];
	 	listResNew := Reduce(listRes);
		return listRes;
	end if;
end intrinsic;


intrinsic PrintStratification(L::[[]], nu, sigma, Np)
	{
		print [[]] containing the polynomials where a residue is 0
	}
	printf "%4o │ %4o/%-4o = %8o ", nu, (sigma*Np), Np, sigma;
	if L eq [[0]] then
		printf "[ 0";
	elif L eq [[1]] then
		printf "[   1";
	elif #L eq 1 then
		l := L[1];
		printf "─"^1*" ";
		for j->f in l do
			printf "\n";
			IndentPush(8);
			printf "(%o)", f;
			IndentPop(8);
			if j lt #l then printf " or "; end if;
		end for;
	else
		printf "─"^0*"┬ ";
		for i->l in L do
			for j->f in l do
				printf "\n";
				IndentPush(8);
				printf "(%o)", f;
				IndentPop(8);
				if j lt #l then printf " or "; end if;
			end for;
			if i lt #L then
				printf "\n"*" "^5*"│"*" "^22*" "^0;
				if i eq (#L-1) then
					printf "└";
				else
					printf "│";
				end if;
				printf " ";//*"& ";
			end if;
		end for;
	end if;
	printf "\n";
end intrinsic;


intrinsic PrintStratificationAsCSV(L::[[]], nu, sigma, Np)
	{
		print [[]] containing the polynomials where a residue is 0
	}
	printf "%4o, %4o/%-4o, %8o, ", nu, (sigma*Np), Np, sigma;
	if L eq [[0]] then
		printf "0";
	elif L eq [[1]] then
		printf "1";
	elif #L eq 1 then
		l := L[1];
		for j->f in l do
			printf "%o", f;
			if j lt #l then printf ", "; end if;
		end for;
	else
		for i->l in L do
			for j->f in l do
				printf "%o", f;
				if j lt #l then printf ", "; end if;
			end for;
			if i lt #L then
				//printf "\n%4o, %4o/%-4o, %8o, ", nu, (sigma*Np), Np, sigma;
				printf "\n,,, ";
			end if;
		end for;
	end if;
	printf "\n";
end intrinsic;


intrinsic PrintStratificationAsLatex(L::[[]], nu, sigma, Np)
	{
		print [[]] containing the polynomials where a residue is 0
	}
	printf "        $%4o $&$ %4o/%-4o =  %8o $&$ ", nu, (sigma*Np), Np, sigma;
	if L eq [[0]] then
		printf "0";
	elif L eq [[1]] then
		printf "1";
	elif #L eq 1 then
		l := L[1];
		for j->f in l do
			sf := Sprint(f);
			//str := (sf[1] eq "t") select "t_" else "";
			//str cat:= &cat[ part cat "t_" : part in Split(sf,"t")];
			str := &cat[ part cat "\\," : part in Split(sf,"*")];
			str := Substring(str, 1, #str-2);
			printf "%o", str;
			if j lt #l then printf "$,$ "; end if;
		end for;
	else
		for i->l in L do
			for j->f in l do
				sf := Sprint(f);
				//str := (sf[1] eq "t") select "t_" else "";
				//str cat:= &cat[ part cat "t_" : part in Split(sf,"t")];
				str := &cat[ part cat "\\," : part in Split(sf,"*")];
				str := Substring(str, 1, #str-2);
				printf "%o", str;
				if j lt #l then printf "$, $ "; end if;
			end for;
			if i lt #L then
				printf "$\\\\ \n               &                         &$ ";
			end if;
		end for;
	end if;
	printf "$\\\\ \\hline  \n";
end intrinsic;


intrinsic ZetaFunctionResidue(arguments::Tup : printType:="none") -> List, List, List, List, List
	{
		Return and print stratification of the residue of the complez zeta function at candidate poles corresponding to nus in rupture divisor r, each one as [[]] which is a sequence of generators of the zero ideal, represented as sequences containing their irreducible factors
	}
	
	// Prepare arguments
	P, xy, pi1, pi2, u, v, lambda, ep, Np, kp, N, k, nus, r, invertibleVariables, printToFile, outFileName := Explode(arguments);
	
	x, y := Explode(xy);
	R := BaseRing(P);
	u /:= Evaluate(u, [0,0]);
	
	// Formal v(x,y) * phi(X,Y) * Z^s, to be evaluated at X=pi1, Y=pi2, Z=u
	Phi := [[[v]]];
	indexs_Phi := {[1,1,1]};
	
	// Storage
	L_all := [**];
	Res_all := [**];
	indexs_Res_all := [**];
	sigma_all := [**];
	epsilon_all := [**];
	
	// print stratification table head
	if (#nus gt 0) then
		if (printType eq "table") then
			printf " nu  │     sigma_{%o,nu}     │ residue=0 => sigma NOT root & (sigma-1) root\n", r;
			printf "─"^5*"┼";
			printf "─"^22*"┼";
			printf "─"^26*"\n";
		elif (printType eq "CSV") then
			printf "nu, sigma, sigma, residue=0 => sigma NOT root & (sigma-1) root\n";
		elif (printType eq "Latex") then
			printf "        $\\nu$&$\\sigma_{%o,\\nu}$&Conditions for $\\Ress{\\sigma_{%o,\\nu}}=0$\\\\", r, r;
			printf "\\hline\\hline\n";
		end if;
	end if;
	
	nuMax := Max([0] cat nus);
	nuOld := 0;
	
	for nu in nus do
		//repeat // Do once, but group statements to calculate time easily
			// Relevant numbers
			sigma := Sigma(Np, kp, nu);
			epsilon := [N[j] * sigma + k[j] : j in [1..3] ];
			
			// // Info regarding the sign of B_p
			// printf "\nepsilon = [ %o, %o, %o ]\n", epsilon[1], epsilon[2], epsilon[3];
			// printf "Fractional part {-eps}: %o, %o, %o\n", FractionalPart(-epsilon[1]), FractionalPart(-epsilon[2]), FractionalPart(-epsilon[3]);
			// RR := RealField();
			// RAprox := RealField(6);
			// printf "cot(pi*(-eps)): %o, %o\n", RAprox!Cot(-Pi(RR)*epsilon[1]), RAprox!Cot(-Pi(RR)*epsilon[3]);
			// printf "cot(pi*(-eps)): %o, %o\n", (Cot(-Pi(RR)*epsilon[1]) gt 0)select"+++"else"---", (Cot(-Pi(RR)*epsilon[3]) gt 0)select"+++"else"---";
			// BFactor := Cot(Pi(RR)*epsilon[1]) + Cot(Pi(RR)*epsilon[3]);
			// printf "cot(pi*eps1)+cot(pi*eps3) = %o%o\n", RAprox!BFactor, (BFactor gt 0)select" !!!!!!"else"";
			
			// Derivative of Phi(pi1(...),pi2(...),u(...); x,y) with respect to x
			Phi, indexs_Phi := FormalDerivativeDiscardingVar(Phi, indexs_Phi, [pi1, pi2, u], nu-nuOld, x, [1, nuMax-nu]);
			nuOld := nu;
			
			DPhi := Phi;
			indexs_DPhi := indexs_Phi;
			// Evaluate at x=0
			EvaluateSeq(~DPhi, ~indexs_DPhi, x, 0);
			
			// Convert d^i/dx^i(Z^s) = (s)*...*(s-i+1)*Z^(s-i)
			for ijk in indexs_DPhi do
				k_idx := ijk[3] - 1; // Number of derivatives of Z^s
				TimesAssignSeqElt(~DPhi, ijk, FallingFactorial(sigma, k_idx));
			end for;
						
			// Expand polynomials depending on power of y
			DPhi_terms := SeparateYTerms(DPhi, indexs_DPhi);
			
			// Calculate residue
			Res, indexs_Res := nonconjugateResidue(DPhi_terms, indexs_DPhi, sigma, lambda, epsilon, ep);
			
			// Basis of the ideal whose roots make the residue =0
			//L := FactorizedBasis(Res, indexs_Res, P, invertibleVariables);
			L := SimplifiedBasis(Res, indexs_Res, P, invertibleVariables);
			
			// Storage
			Append(~L_all, L);
			Append(~Res_all, Res);
			Append(~indexs_Res_all, indexs_Res);
			Append(~sigma_all, <r, nu,sigma>);
			Append(~epsilon_all, epsilon);
			
			// print
			
			if (printType ne "none") then
				printf "sigma_{%o,%o}=%o\n", r, nu, sigma;
				for AIdx->ij in Sort([elt : elt in indexs_Res]) do
					printf "[%o,%o]\n", ij[1], ij[2];
					IndentPush();
					printf "%o\n", SeqElt(Res,ij);
					IndentPop();
				end for;
				printf "Simplified:\n";
				print L;
				printf "\n";
			end if;
			// if (printType eq "table") then
			// 	PrintStratification(L, nu, sigma, Np);
			// elif (printType eq "CSV") then
			// 	PrintStratificationAsCSV(L, nu, sigma, Np);
			// elif (printType eq "Latex") then
			// 	PrintStratificationAsLatex(L, nu, sigma, Np);
			// end if;
			// print Res;
			
			// Flush to file
			if printToFile then
				UnsetOutputFile();
				SetOutputFile(outFileName : Overwrite := false);
			end if;
			
		//until true;
	end for;
	
	if (printType ne "none") then
		printf "\n";
	end if;
	
	return L_all, Res_all, indexs_Res_all, sigma_all, epsilon_all;
end intrinsic;


// Changes of variables

intrinsic DiscardHigherPow(f, var, pow::RngIntElt) -> Any
	{
		Discard terms with powers of var higher than var^pow
	}
	return &+[Parent(f) | t : t in Terms(f) | Degree(t, var) le pow];
end intrinsic;


intrinsic Evaluate(f::FldFunRatMElt, i::RngIntElt, r::RngElt) -> FldFunRatMElt
	{
		Evaluate a multivariate rational function in x_i=r
		Necessary in construction of curve from _betas
	}
	return Evaluate(Numerator(f), i, r) / Evaluate(Denominator(f), i, r);
end intrinsic;


// Full stratification

intrinsic ZetaFunctionStratification(
	f::RngMPolLocElt, planeBranchNumbers::Tup, nuChoices::SeqEnum :
	invertibleVariables:=[],
	printType:="none",
	printToFile:=false,
	outFileName:=""
) -> List, List, List, List, List
	{
		TO DO
	}
	
	// Prepare arguments
	P<x,y> := Parent(f);
	R := BaseRing(P);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	
	ignoreDivisor := [ nuChoices[i] eq [] : i in [1..g] ];

	// (total transform of f) = x^xExp_f * y^yExp_f * units_f * strictTransform_f
	// (pullback of dx^dy)    = x^xExp_w * y^yExp_w * units_w
	strictTransform_f := f;
	xyExp_f := [0,0];
	xyExp_w := [0,0];
	units_f := {* P!1 *};
	units_w := {* P!1 *};
	pointType := 0; // 0 -> starting point, 1 -> free point, 2 -> satellite point
	PI_TOTAL := [x, y]; // Total blowup morphism since starting point
	L_all := [**];
	Res_all := [**];
	indexs_Res_all := [**];
	sigma_all := [**];
	epsilon_all := [**];
	
	// ### For each rupture divisor ###
	// Non-rupture divisors don't contribute (see TFG-Roger, p.28, Cor.4.2.5 or PHD-Guillem p.87 Th.8.10)
	for r in [1..g] do
		print "\n------------------------------";
		if (printType ne "none" and not ignoreDivisor[r]) then printf "Divisor E_%o\n", r; end if;
		
		///////////////////////////////// THEORY OK ////////////////////////////////////
		
		// Blowup
		// From: (0,0) singular point of the strict transform of the curve (starting point or a free point on the last rupture divisor)
		// To: next rupture divisor
		strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType, lambda, ep, PI_blowup := Blowup(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType);
		// Total blowup morphism since starting point
		PI_TOTAL := [Evaluate(t, PI_blowup) : t in PI_TOTAL];
		// Units
		u := &*[t^m : t->m in units_f] * strictTransform_f;
		v := &*[t^m : t->m in units_w];
		// Multiplicities of rupture divisor x=0
		Np := xyExp_f[1];
		Kp := xyExp_w[1];
		// Multiplicities of y=0
		N1 := xyExp_f[2];
		K1 := xyExp_w[2];
		// Multiplicities of:
		// 1) proximate non-rupture divisor through (0,0): y=0
		// 2) proximate non-rupture divisor through (0,infinity)
		// 3) the curve
		N := [N1, Np-N1-ep, ep];
		k := [K1, Kp-K1-1, 0];
		
		// printf "u = %o\n\n", u;
		// printf "v = %o\n\n", v;
		// printf "PI_TOTAL = %o\n\n", PI_TOTAL;
		// printf "e = %o\n", ep;
		// printf "k = %o\n", ks;
		
		// // Find the maximum nu in this and following rupture divisors => maximum power needed in series expansions in x (?????????)
		// // Don't discard topological roots to have enough terms for a blowup
		// M := 0;
		// for i in [r..g] do
		// 	Npi, kpi, Ni, ki := MultiplicitiesAtThisRuptureDivisor(i, Nps, kps, Ns, ks);
		// 	M := Max( [M] cat Nus(_betas, semiGroupInfo, Npi, kpi, i : discardTopologial:=false) );
		// end for;
		
		// Interesting values of nu
		// nus := Nus(_betas, semiGroupInfo, Np, Kp, r : discardTopologial:=true);
		// nus, topologicalNus := Nus(_betas, semiGroupInfo, Np, Kp, r : discardTopologial:=true);
		// topologicalRoots[r] := [<nu, Sigma(Np, Kp, nu)> : nu in topologicalNus];
		
		//if useDefaultNus[r] then
		//	nus := defaultNus[r];
		//else
		nus := nuChoices[r];
		//end if;
		
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
		
		print "------------------------------";
		print "ZetaFunctionResidue";
		
		// Flush to file
		if printToFile then
			UnsetOutputFile();
			SetOutputFile(outFileName : Overwrite := false);
		end if;
		
		L_all[r], Res_all[r], indexs_Res_all[r], sigma_all[r], epsilon_all[r] := ZetaFunctionResidue(< P, [x,y], PI_TOTAL[1], PI_TOTAL[2], u, v, lambda, ep, Np, Kp, N, k, nus, r, invertibleVariables, printToFile, outFileName > : printType:=printType);
		
		// Flush to file
		if printToFile then
			UnsetOutputFile();
			SetOutputFile(outFileName : Overwrite := false);
		end if;
		
		// Prepare next iteration
		if r lt g then
			print "------------------------------";
			print "Centering the singular point";
			
			strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, PI_center := CenterOriginOnCurve(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, lambda);
			// Total blowup morphism since starting point
			PI_TOTAL := [Evaluate(t, PI_center) : t in PI_TOTAL];
			
			printf "lambda = %o\n\n", lambda;
		end if;
	end for;
	
	return L_all, Res_all, indexs_Res_all, sigma_all, epsilon_all;
end intrinsic;

