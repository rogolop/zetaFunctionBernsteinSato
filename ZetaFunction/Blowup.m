/*
	Author: Roger Gomez Lopez
	
	Blowups, transforms, information derived from the semigroup
*/

// Information related to the curve and its blowup(s)

function MatToSeq(M)
	// Sequence containing all matrix elements (preserving index if size is 1xN or Nx1)
	return [ M[i,j] : i in [1..Nrows(M)], j in [1..Ncols(M)] ];
end function;


intrinsic SemiGroupInfo(_betas::[]) -> Tup
	{
		Numbers related to the semigroup and the characteristic exponents.
		Input: _betas -> generators of the semigroup
		Theory indexing of all sequences 0..g -> Magma indexing 1..(g+1)
	}
	g := #_betas - 1; // Number of characteristic exponents (see PHD-Guillem, p.25)
	n := _betas[1]; // Multiplicity of the curve at the origin (see PHD-Guillem, p.24)
	
	charExpsData := CharExponents(_betas); // [<beta_i,e_i>] with e_i at starting point and rupture divisors
	betas := [cExp[1] : cExp in charExpsData]; // defining beta_0=0
	es := [cExp[2] : cExp in charExpsData];
	
	ms := [betas[i] div es[i] : i in [1..g+1]]; // defining m_0=0, m_i=beta_i/e_i (see PHD-Guillem, p.24)
	ns := [0] cat [es[i-1] div es[i] : i in [2..g+1]]; // n_0=0, n_i=e_{i-1}/e_i (see PHD-Guillem, p.24)
	_ms := [_betas[i] div es[i] : i in [1..g+1]]; // _m_i=_beta_i/e_i (see PHD-Guillem, p.25)
	qs := [0] cat [ms[i] - ns[i]*ms[i-1] : i in [2..g+1]]; // q_i=m_i-n_i*m_{i-1} (see PHD-Guillem, p.25)
	c := ns[g+1]*_betas[g+1] - betas[g+1] - (n-1); // Conductor of the semigroup / Milnor number, c=n_g*_beta_g-beta_g-(n-1) (see PHD-Guillem, p.25)

	// Characteristic exponents
	//[betas[i] / n : i in [1..g+1]];
	//[ms[i] / &*(ns[2..i+1]) : i in [1..g+1]];
	//PuiseuxExpansionReduced(f);
	
	return < g, c, betas, es, ms, ns, qs, _ms >;
end intrinsic;


intrinsic MultiplicitiesAtAllRuptureDivisors(_betas::[]) -> [], [], [], []
	{
		Multiplicities of the rupture divisors and their adjacent divisors
	}
	// All multiplicities
	ProxMat, e := ProximityMatrix(_betas : ExtraPoint := true); // e: strict transform multiplicities
	N := e*Transpose(ProxMat^(-1)); // (see TFG-Roger, p.16, Prop.2.3.21)
	ones := Matrix([[1 : i in [1..Ncols(ProxMat)]]]); // row matrix (1,...,1)
	k := ones*Transpose(ProxMat^(-1)); // (see TFG-Roger, p.17, Prop.2.3.22)
	e := MatToSeq(e); // e: strict transform multiplicities
	N := MatToSeq(N); // N: total transform multiplicities
	k := MatToSeq(k); // k: canonical divisor multiplicities
	
	// Multiplicities at rupture divisors
	E := -Transpose(ProxMat)*ProxMat; // Dual graph matrix / intersection matrix (see TFG-Roger, p.18, Def.2.3.23)
	EE := RowSequence(E - DiagonalMatrix(Integers(), Diagonal(E))); // Remove diagonal, now EE[i][j]=1 if i!=j and Ei intersects Ej, else EE[i][j]=0
	Rup := [i : i in [1..Ncols(ProxMat)] | &+EE[i] ge 3]; // Rupture divisors' indexes (divisors with >=3 intersections)
	Nps := N[Rup]; // N of rupture divisors
	kps := k[Rup]; // k of rupture divisor
	
	// Multiplicities of divisors adjacent to each rupture divisor
	Ns := [];
	ks := [];
	for p in Rup[1..#Rup] do
		Adj_p := [i : i in [1..Ncols(ProxMat)] | E[p][i] eq 1]; // indexes of divisors adjacent to each rupture divisor (they intersect)
		Append(~Ns, N[Adj_p]); // N's of adjacent divisors
		Append(~ks, k[Adj_p]); // k's of adjacent divisors
		Ns[#Ns,3] := e[p]; // e of the curve (see TFG-Roger, p.27, Def.4.2.1, from PHD-Guillem p.81 Def 8.2 together with p.89 at eq. 9.2)
		ks[#ks,3] := 0; // k of the curve (see TFG-Roger, p.27, Def.4.2.1, from PHD-Guillem p.81 Def 8.2 together with p.89 at eq. 9.2)
	end for;
	
	return Nps, kps, Ns, ks;
end intrinsic;


intrinsic MultiplicitiesAtThisRuptureDivisor(r::RngIntElt, Nps::[], kps::[], Ns::[], ks::[]) -> RngIntElt, RngIntElt, [], []
	{
		Multiplicities of the r-th rupture divisor and its adjacent divisors
	}
	Np := Nps[r]; // N of rupture divisor
	kp := kps[r]; // k of rupture divisor
	N := Ns[r]; // N's of adjacent divisors
	k := ks[r]; // k's of adjacent divisors
	return Np, kp, N, k;
end intrinsic;


function SemigroupElements(G, mu)
	// Elements of the semigroup G up to (including) mu
	if #G eq 0 or mu lt 0 then return {}; end if;
	L := {G[1]*i : i in [0..Floor(mu/G[1])]};
	if #G eq 1 then return L; end if;
	semigroupElements := {};
	for a in L do
		semigroupElements join:= {a+b : b in SemigroupElements(G[2..#G], mu-a)};
	end for;
	return semigroupElements;
end function;

intrinsic Nus(_betas, semiGroupInfo, Np, kp, r : discardTopologial:=true) -> [], []
	{
		Values of nu which may correspond to a varying root of the Bernstein-Sato polynomial, and topological roots
	}
	g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
	
	// All possible nus (see TFG-Roger, p.29, Cor.4.2.12)
	nus := [0..(Np-1)];
	
	// Discard nus corresponding to the other divisors crossing the r-th exceptional divisor (they never correspond to roots of the Bernstein-Sato-polynomial, and they may give infinities and zeros at the calculation of the residue of the complex zeta function)
	// Conditions: _beta_r*sigma not integer
	//             e_{r-1}*sigma not integer
	// (see TFG-Roger, p.28, Th.4.2.6)
	Z := IntegerRing();
	nus := [nu : nu in nus | _betas[r+1]*Sigma(Np,kp,nu) notin Z and es[r]*Sigma(Np,kp,nu) notin Z ];
	
	// Topological roots of Bernstein-Sato polynomial: 
	// - they are roots for any topologically trivial deformation
	// - they give unit (=> nonzero) residues of the complex zeta function (see TFG-Roger, p.28-29)
	//
	// Their nus correspond to:
	//   semigroup of the divisorial valuation of Er
	//   == semigroup of the (r+1)-th maximal contact element
	// 
	// Beware the inconsistent notation Gamma_i:
	// 1) PHD-Guillem p.120 Theorem 12.3 -> top. roots sigma_i -> Gamma_i: Ei
	// 2) PHD-Guillem p.26 eq.2.22 -> Gamma_i: fi i-th max contact
	//    PHD-Guillem p.26 Lemma 2.10 -> Gamma_i: fi i-th max contact, E_{i-1}
	//    PHD-Guillem p.31 eq.2.43) -> Gamma_{i+1}: Ei => Gamma_i: fi
	// 3) TFG-Roger p.28 eq.4.2.9 AND ALL FOLLOWING RESULTS -> Gamma_i: Ei
	// 4) TFG-Roger p.29 eq.4.2.10 -> Gamma_i: fi => WRONG DEFINITION
	//
	// Define as in 1) and 3) -> Gamma_i: Ei
	//
	// Gamma_r = < 
	//   (n_1*n_2*...*n_r) * _m_0,
	//       (n_2*...*n_r) * _m_1,
	//                 ...
	//               (n_r) * _m_{r-1},
	//                  () * _m_r
	// >
	// = < n_{j+1}*...*n_r * _m_j | j = 0,...,r >
	//
	Gamma_r := [ &*(ns[[(j+2)..(r+1)]]) * _ms[j+1] : j in [0..r] ];
	while 0 in Gamma_r do Exclude(~Gamma_r, 0); end while; // Remove all 0's in Gamma_r
	
	mu_r := ns[r+1] * _ms[r+1] - ms[r+1] - &*(ns[2..(r+1)]) + 1;
	Gamma_r_elements := SemigroupElements(Gamma_r, mu_r);
	topologicalNus := [nu : nu in nus | nu in Gamma_r_elements or nu gt mu_r];
	// topologicalNus := [nu : nu in nus | SemiGroupMembership(nu, Gamma_r)];
	
	if discardTopologial then
		nus := [nu : nu in nus | nu notin topologicalNus];
	end if;
	
	return nus, topologicalNus;
end intrinsic;


intrinsic Sigma(Np::RngIntElt, kp::RngIntElt, nu::RngIntElt) -> FldRatElt
	{
		Root candidate corresponding to a nu
	}
	return - (kp + 1 + nu) / Np; // (see TFG-Roger p.27 eq.4.2.1)
end intrinsic;


// Blowup and centering

function xFactor(f)
	// Exponent of common factor x in f (f != 0)
	return Min([IntegerRing() | Exponents(term)[1] : term in Terms(f)]);
end function;


function yFactor(f)
	// Exponent of common factor y in f (f != 0)
	return Min([IntegerRing() | Exponents(term)[2] : term in Terms(f)]);
end function;


function strictPart(f)
	// Separate factors x^A and y^B from f (might result in 1)
	P := Parent(f); x := P.1; y := P.2;
	
	A := xFactor(f);
	B := yFactor(f);
	return ExactQuotient(f, x^A*y^B), A, B;
end function;


function TangentTerm(f)
	// Terms of lowest degree of f, excluding factors x,y
	P := Parent(f); x := P.1; y := P.2;
	
	// assert f eq strictPart(f);
	
	// Simultaneously search lowest degree and store monomials of that degree
	ms := Monomials(f);
	tan := 0;
	min_deg := Infinity();
	for m in ms do
		deg := Degree(m);
		if deg lt min_deg then
			min_deg := deg;
			tan := MonomialCoefficient(f, m) * m;
		elif deg eq min_deg then
			tan +:= MonomialCoefficient(f, m) * m;
		end if;
	end for;
	return tan;
end function;


intrinsic Blowup(strictTransform_f::RngMPolLocElt, xyExp_f::[], xyExp_w::[], units_f::SetMulti, units_w::SetMulti, pointType::RngIntElt) -> RngMPolLocElt, [], [], SetMulti, SetMulti, RngIntElt, FldElt, RngIntElt, []
	{
		Blowup from one rupture divisor to the next one
		
		(total transform of f) = x^xExp_f * y^yExp_f * units_f * strictTransform_f
		(pullback of dx^dy)    = x^xExp_w * y^yExp_w * units_w
		
		pointType:  0 -> starting point, 1 -> free point, 2 -> satellite point
		(0,lambda): intersection of rupture divisor and strict transform after last blowup
		e:          multiplicity of the strict transform
		PI_blowup:  blowup morphism from one rupture divisor to the next one
		
		Assumptions and conventions:
		- point to blow up: (0,0)
		- previous exceptional divisor (at free and satellite points): x=0
		- the other crossing exceptional divsor (at satellite points): y=0
		- strictTransform_f may have any tangent
	}
	P := Parent(strictTransform_f); x := P.1; y := P.2; R := BaseRing(P);
	xExp_f, yExp_f := Explode(xyExp_f);
	xExp_w, yExp_w := Explode(xyExp_w);
	
	blownUpRupture := false;
	lambda := R!0;
	e := 0;
	PI_blowup := [x, y];
	
	while (not blownUpRupture) do
		tan := TangentTerm(strictTransform_f);
		
		if (Length(tan) eq 1) then
			if (Exponents(tan)[1] gt 0) then
				// Case tan = C * x^e
				pi := [x*y, x];
				PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
				
				// x^xExp * y^yExp -> (x*y)^xExp * x^yExp = x^(xExp+yExp) * y^xExp
				xExp_f, yExp_f := Explode(< xExp_f + yExp_f, xExp_f >);
				xExp_w, yExp_w := Explode(< xExp_w + yExp_w, xExp_w >);
				
				// Blow up each term, preserve multiplicity
				// They are units and will be units after blowups: no common x,y
				units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
				units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
				
				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
				xExp_f +:= A;
				yExp_f +:= B;
				
				// Pullback of dx^dy by pi
				// Ignoring multiplicative constant (-1) in w
				xExp_w +:= 1;
				
				if (pointType eq 0) then
					pointType := 1;
				else
					pointType := 2;
				end if;
				
			else
				// Case tan = C * y^e
				pi := [x, x*y];
				PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
				
				// x^xExp * y^yExp -> x^xExp * (x*y)^yExp = x^(xExp+yExp) * y^yExp
				xExp_f, yExp_f := Explode(< xExp_f + yExp_f, yExp_f >);
				xExp_w, yExp_w := Explode(< xExp_w + yExp_w, yExp_w >);
				
				// Blow up each term, preserve multiplicity
				// They are units and will be units after blowups: no common x,y
				units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
				units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
				
				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
				xExp_f +:= A;
				yExp_f +:= B;
				
				// Pullback of dx^dy by pi
				xExp_w +:= 1;
				
				if (pointType eq 2) then
					pointType := 2;
				else
					pointType := 1;
				end if;
				
			end if;
		else
			// Case tan = C * (x-lambda*y)^e, lambda =/= 0
			
			// Lambda
			e := Degree(tan, y);
			C := MonomialCoefficient(tan, x^e);
			// tan = C*x^e - C*e*lambda*x^(e-1)*y + ...
			lambda := MonomialCoefficient(tan, x^(e-1)*y) / (- C * e);
			
			pi := [x, x*y];
			
			PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
			
			// x^xExp * y^yExp -> x^xExp * (x*y)^yExp = x^(xExp+yExp) * y^yExp
			xExp_f, yExp_f := Explode(< xExp_f + yExp_f, yExp_f >);
			xExp_w, yExp_w := Explode(< xExp_w + yExp_w, yExp_w >);
			
			// Blow up each term, preserve multiplicity
			// They are units and will be units after blowups: no common x,y
			units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
			units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
			
			strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
			xExp_f +:= A;
			yExp_f +:= B;
			
			// Pullback of dx^dy by pi
			xExp_w +:= 1;
			
			if (pointType eq 2) then
				pointType := 1;
				blownUpRupture := true;
			else
				pointType := 1;
				
				// Center intersecion with current exceptional divisor to (0,0)
				
				pi := [x, (1-y)/lambda];
				PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
				
				// Change variables of each term, preserve multiplicity
				// They are units and will be units after change of variables
				// because the point is free: no common x,y
				units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
				units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
				
				// x^xExp * y^yExp -> x^xExp * ((1-y)/lambda)^yExp
				Include(~units_f, (pi[2])^^yExp_f);
				Include(~units_w, (pi[2])^^yExp_w);
				yExp_f := 0;
				yExp_w := 0;
				
				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
				xExp_f +:= A;
				yExp_f +:= B;
				
				// Pullback of dx^dy by pi
				// Ignoring multiplicative constant (-1/lambda) in w
			end if;
		end if;
	end while;
	
	return strictTransform_f, [xExp_f,yExp_f], [xExp_w,yExp_w], units_f, units_w, pointType, lambda, e, PI_blowup;
end intrinsic;


intrinsic CenterOriginOnCurve(strictTransform_f::RngMPolLocElt, xyExp_f::[], xyExp_w::[], units_f::SetMulti, units_w::SetMulti, lambda::FldElt) -> RngMPolLocElt, [], [], SetMulti, SetMulti, []
	{
		Change y variable moving (0, 1/lambda) to (0,0)
		
		Sends (0,0) to (0,1), (0,infinity) to (0,infinity)
	}
	P := Parent(strictTransform_f); x := P.1; y := P.2; R := BaseRing(P);
	xExp_f, yExp_f := Explode(xyExp_f);
	xExp_w, yExp_w := Explode(xyExp_w);
	
	// Center intersecion with current exceptional divisor to (0,0)
	
	pi := [x, (1-y)/lambda];
	
	// Change variables of each term, preserve multiplicity
	// They are units and will be units after change of variables
	// because the point is free: no common x,y
	units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
	units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
	
	// x^xExp * y^yExp -> x^xExp * ((1-y)/lambda)^yExp
	Include(~units_f, (pi[2])^^yExp_f);
	Include(~units_w, (pi[2])^^yExp_w);
	yExp_f := 0;
	yExp_w := 0;
	
	strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
	xExp_f +:= A;
	yExp_f +:= B;
	
	// Pullback of dx^dy by pi
	// Ignoring multiplicative constant (-1/lambda) in w
	
	return strictTransform_f, [xExp_f,yExp_f], [xExp_w,yExp_w], units_f, units_w, pi;
end intrinsic;




