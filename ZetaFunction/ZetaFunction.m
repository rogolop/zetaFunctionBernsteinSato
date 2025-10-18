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


intrinsic SimplifiedBasis(Res::[], indexs_Res::{}, P::RngMPolLoc, assumeNonzero::{}) -> []
	{
		Get a simplified basis of polynomials
	}
	debugPrint := false;
	
	R := BaseRing(P); // P = R[x,y]
	if #indexs_Res eq 0 then return [R| 0]; end if;
	
	// Ignore which derivative of delta-function
	listRes := [P | SeqElt(Res, ij) : ij in Sort([IJ : IJ in indexs_Res]) ];
	
	// Check that the residues have no terms with x,y => residues are in R
	error if (&or[TotalDegree(res) gt 0 : res in listRes]), "At SimplifiedBasis(Res, indexs_Res, P, assumeNonzero): Res contains x or y\nGiven arguments:", Res, ",", indexs_Res, ",", P, ",", assumeNonzero;
	listRes := [R| MonomialCoefficient(res, P!1) : res in listRes]; // residues are equal to the constant term in x,y
	
	if Type(R) eq FldFunRat then // R = Q(t_1,...,t_k)
		// Clear denominators while checking that they are nonzero
		for idx->res in listRes do
			denom := Denominator(res);
			denomFactorization := Factorization(denom);
			for tup in denomFactorization do
				factor, exponent := Explode(tup);
				if factor notin assumeNonzero then
					error "At SimplifiedBasis(): Residue has a denominator that may be zero. If it is nonzero, please add it to assumeNonzero.\nResidue term =\n", res, ", denominator factor=\n", factor;
				end if;
			end for;
			listRes[idx] *:= denom;
		end for;
		// Change ring to Q[t_1,...,t_k] and simplify the basis of the ideal
		ChangeUniverse(~listRes, RingOfIntegers(R));
		listRes := Reduce(listRes);
		return listRes;
	elif R eq Rationals() then
		listRes := [R| res : res in listRes | res ne 0];
		if #listRes gt 0 then
			return [R| 1];
		else
			return [R| 0];
		end if;
	else
		//listRes := [R| res : res in listRes | not IsUnit(res)];
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


intrinsic ZetaFunctionResidue(arguments::Tup : verboseLevel:="none") -> List, List, List, List, List
	{
		Return and print stratification of the residue of the complez zeta function at candidate poles corresponding to nus in rupture divisor r, each one as [[]] which is a sequence of generators of the zero ideal, represented as sequences containing their irreducible factors.
		
		verboseLevel: "none", "default", "onlyStrata", or "detailed"
	}
	
	// Prepare arguments
	P, xy, pi1, pi2, u, v, lambda, ep, Np, kp, N, k, nus, r, assumeNonzero := Explode(arguments);
	
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
			
			// print
			if verboseLevel in {"default", "onlyStrata", "detailed"} then
				printf "sigma_{%o,%o}=%o\n", r, nu, sigma;
				if verboseLevel in {"detailed"} then
					for AIdx->ij in Sort([elt : elt in indexs_Res]) do
						printf "[%o,%o]\n", ij[1], ij[2];
						IndentPush();
						printf "%o\n", SeqElt(Res,ij);
						IndentPop();
					end for;
					printf "Simplified:\n";
				end if;
			end if;
			
			// Basis of the ideal whose roots make the residue =0
			L := SimplifiedBasis(Res, indexs_Res, P, assumeNonzero);
			
			// Storage
			Append(~L_all, L);
			Append(~Res_all, Res);
			Append(~indexs_Res_all, indexs_Res);
			Append(~sigma_all, <r, nu,sigma>);
			Append(~epsilon_all, epsilon);
			
			// print
			if verboseLevel in {"default", "onlyStrata", "detailed"} then
				print L;
				printf "\n";
			end if;
		//until true;
	end for;
	
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
	assumeNonzero:={},
	verboseLevel:="default"
) -> List, List, List, List, List, {}
	{
		TO DO
		
		verboseLevel: "none", "default", "onlyStrata", or "detailed"
	}
	debugPrint := false;
	
	// Prepare arguments
	P<x,y> := Parent(f);
	R := BaseRing(P);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	if Type(R) eq FldFunRat then
		assumeNonzero := {RingOfIntegers(R)| tup[1] : tup in Factorization(Numerator(h)) cat Factorization(Denominator(h)), h in assumeNonzero};
	end if;
	if debugPrint then printf "assumeNonzero =\n"; print assumeNonzero; end if;
	//error if &or[g notin RingOfIntegers(R) : g in assumeNonzero], "At ZetaFunctionStratification(): assumeNonzero contains elements with denominators";
	
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
		if (verboseLevel in {"default", "onlyStrata", "detailed"}) then
			printf "_______________________________________________________________________\n";
			printf "Divisor E_%o\n\n", r;
		end if;
		
		// Blowup
		// From: (0,0) singular point of the strict transform of the curve (starting point or a free point on the last rupture divisor)
		// To: next rupture divisor
		strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType, lambda, PI_blowup, assumeNonzero := Blowup(strictTransform_f, xyExp_f cat xyExp_w, units_f, units_w, pointType, assumeNonzero : verboseLevel:=verboseLevel);
		if debugPrint then printf "assumeNonzero =\n"; print assumeNonzero; end if;
		if (verboseLevel in {"default", "detailed"}) then
			printf "lambda = %o\n", lambda;
		end if;
		
		ep := es[r];
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
		
		nus := nuChoices[r];
		
		if (verboseLevel in {"default", "detailed"}) then
			printf "nus = %o\n\n", nuChoices[r];
		end if;
		
		L_all[r], Res_all[r], indexs_Res_all[r], sigma_all[r], epsilon_all[r] := ZetaFunctionResidue(< P, [x,y], PI_TOTAL[1], PI_TOTAL[2], u, v, lambda, ep, Np, Kp, N, k, nus, r, assumeNonzero > : verboseLevel:=verboseLevel);
		
		// Prepare next iteration
		if r lt g then
			if (verboseLevel in {"detailed"}) then
				printf "_______________________________________________________________________\n";
				printf "Centering the singular point\n";
			end if;
			
			strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, PI_center, assumeNonzero := CenterOriginOnCurve(strictTransform_f, xyExp_f cat xyExp_w, units_f, units_w, lambda, assumeNonzero : verboseLevel:=verboseLevel);
			if debugPrint then printf "assumeNonzero =\n"; print assumeNonzero; end if;
			// Total blowup morphism since starting point
			PI_TOTAL := [Evaluate(t, PI_center) : t in PI_TOTAL];
		end if;
	end for;
	
	return L_all, Res_all, indexs_Res_all, sigma_all, epsilon_all, assumeNonzero;
end intrinsic;



intrinsic ZetaFunctionStratificationDefault(
	f::RngMPolLocElt :
	assumeNonzero:={},
	verboseLevel:="default"
) -> List, List
	{
		TO DO
		
		verboseLevel: "none", "default", "onlyStrata", or "detailed"
	}
	_betas := SemiGroup(f);
	planeBranchNumbers := PlaneBranchNumbers(_betas);
	nusForPoleCandidates, nusForRootCandidatesIncludingUndetermined, nusIncludingTopological, trueNonTopSigmas, coincidingTopAndNonTopSigmas, otherTopologicalSigmas, nonTopSigmaToIndexList, topologicalSigmaToIndexList, trueNonTopSigmasCoincidences, otherTopologicalSigmasCoincidences := CandidatesData(planeBranchNumbers);
	nuChoices := nusForPoleCandidates;
	
	L_all, Res_all, indexs_Res_all, sigma_all, epsilon_all := ZetaFunctionStratification(
		f, planeBranchNumbers, nuChoices :
		assumeNonzero:=assumeNonzero,
		verboseLevel:=verboseLevel
		);
	
	return L_all, sigma_all;
end intrinsic;


