/*
	Author: Roger Gomez Lopez
	
	Modified functions for working with all possibilities (instead of choosing one automatically)
	for the semigroup coordinates, monomial curves, and deformations
*/
// import "Blowup.m": SemiGroupInfo; // WHY NOT ???


intrinsic allSemigroupCoordinates(v::RngIntElt, G::SeqEnum[RngIntElt]) -> BoolElt, SeqEnum
	{
		Calculate all possible coordinates of v as member of the (additive) semigroup with generators G
	}
	require v ge 0: "Negative first argument.";
	
	// Base case: G = [ G[1] ]
	if #G eq 1 then
		divisible, quotient := IsDivisibleBy(v, G[1]);
		if divisible then
			return true, [ [quotient] ];
		else
			return false, [ ];
		end if;
	end if;
	
	// Recursive case
	V1 := 0; // First coordinate
	Results := []; // To gather all possible coordinates of v in G
	GNext := G[2..#G]; // G without G[1]
	while G[1]*V1 le v do
		// Given fixed V1, calculate all possible remaining coordinates V2 to V_{#G}
		isPossible, possibilities := allSemigroupCoordinates(v - G[1]*V1, GNext);
		if isPossible then
			Results cat:= [ [V1] cat coord : coord in possibilities ]; // Save found coordinates [V1, V2, ..., V_{#G}]
		end if;
		// Increase V1
		V1 +:= 1;
	end while;
	
	return #Results gt 0, Results;
end intrinsic;


intrinsic allMonomialCurves(G::SeqEnum[RngIntElt]) -> SeqEnum[SeqEnum[RngMPolElt]]
	{
		Computes all monomial curves assocaited to a semigroup of a plane curve.
		Output: eqs = [[possible i-th equations]]
		A curve is determined by choosing one equation of each eqs[i].
		Implementation based on "MonomialCurve(G::[RngIntElt])" from "SingularitiesDim2/Misc.m"
	}
	require IsPlaneCurveSemiGroup(G): "G is not the semigroup of a plane curve";
	
	// Copied:
	E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
	N := [E[i - 1] div E[i] : i in [2..#G]];
	R := PolynomialRing(RationalField(), G);
	AssignNames(~R, ["u" cat IntegerToString(i) : i in [0..#G - 1]]);
	
	// Store all semigroup coordinates for each i instead of only one L_i
	Ls := [];
	for i in [1..#G - 1] do // Copied
		_, Ls[i] := allSemigroupCoordinates(N[i] * G[i + 1], G[[1..i]]); // Instead of using "SemiGroupMembership(N[i] * G[i + 1], G[[1..i]])"
	end for;
	
	// Store all equations for each i instead of only one
	eqs := [];
	for i in [1..#G - 1] do // Copied
		eqs[i] := [];
		for L_i in Ls[i] do
			eqs[i] cat:= [ R.(i + 1)^N[i] - &*[R.j^L_i[j] : j in [1..i]] ]; // Copied
		end for;
	end for;
	return eqs;
end intrinsic;





function ExponentSetE(l, n)
	return [ [i,j] : i in [0..(l[1][0+1] - 2)], j in [0..(n[1] - 2)] ];
end function;

forward ExponentSetDplSTm1;

function ExponentSetIlSTm2(s, t, l, n)
	// 2 <= t <= s
	if t eq 2 then
		return [ [i,j] : i in [0..(l[s][0+1] - 1)],
		                 j in [0..(n[1] - 1)] ];
	end if;
	DplSTm2 := ExponentSetDplSTm1(s, t - 1, l, n);
	return [ kk cat [kTm1] : kk in DplSTm2,
													 kTm1 in [0..(n[t-1] - 1)] ];
end function;


function ExponentSetJlSTm1(s, t, l, n)
	// 2 <= t <= s
	if t eq 2 then
		return [ [i,j] : i in [(l[s][0+1])..(l[s][0+1] + l[1][0+1] -1)],
		                 j in [0..(l[s][1+1] - 1)] ];
	end if;
	DplTm1Tm2 := ExponentSetDplSTm1(t - 1, t - 1, l, n);
	shiftedDplTm1Tm2 := [ [ kk[idx] + l[s][idx] : idx in [1..#kk] ] : kk in DplTm1Tm2 ];
	return [ kk cat [kTm1] : kk in shiftedDplTm1Tm2,
	                         kTm1 in [0..(l[s][t-1+1] - 1)] ];
end function;


function ExponentSetDplSTm1(s, t, l, n)
	// 2 <= t <= s
	IlSTm2 := ExponentSetIlSTm2(s, t, l, n);
	if l[s][t-1+1] eq 0 then
		return IlSTm2;
	end if;
	JlSTm1 := ExponentSetJlSTm1(s, t, l, n);
	return IlSTm2 cat JlSTm1;
end function;


function ExponentSetDlSSm1(s, l, n)
	// 2 <= s
	IlSSm2 := ExponentSetIlSTm2(s, s, l, n);
	if l[s][s-1+1] eq 0 then
		Exclude(~IlSSm2, Max(IlSSm2));
		return IlSSm2;
	end if;
	JlSSm1 := ExponentSetJlSTm1(s, s, l, n);
	DlSSm1 := IlSSm2 cat JlSSm1;
	Exclude(~DlSSm1, Max(JlSSm1));
	return DlSSm1;
end function;


intrinsic SemigroupCoordinatesCassouNogues(v::RngIntElt, G::SeqEnum[RngIntElt], n::SeqEnum) -> BoolElt, SeqEnum
	{
		Calculate the coordinates of v as member of the (additive) semigroup with generators G,
		with the criterion of being less than the corresponding n_i (except maybe the first coordinate)
	}
	require v ge 0: "Negative first argument.";
	
	// Base case: G = [ G[1] ]
	if #G eq 1 then
		divisible, quotient := IsDivisibleBy(v, G[1]);
		if divisible then
			if (n[1] gt 0) and (quotient ge n[1]) then return false, [ ]; end if; // enforce v_i < n_i (except at index 0, where n_0 = n[1] = 0)
			return true, [ [quotient] ];
		else
			return false, [ ];
		end if;
	end if;
	
	// Recursive case
	V1 := 0; // First coordinate
	Results := []; // To gather all possible coordinates of v in G
	GNext := G[2..#G];
	nNext := n[2..#n];
	while G[1]*V1 le v do
		if (n[1] gt 0) and (V1 ge n[1]) then break; end if; // enforce v_i < n_i (except at index 0, where n_0 = n[1] = 0)
		// Given fixed V1, calculate remaining coordinates V2 to V_{#G}
		inSemigroup, possibilities := SemigroupCoordinatesCassouNogues(v - G[1]*V1, GNext, nNext);
		if inSemigroup then
			Results cat:= [ [V1] cat coord : coord in possibilities ]; // Save found coordinates [V1, V2, ..., V_{#G}]
		end if;
		V1 +:= 1;
	end while;
	
	return #Results gt 0, Results;
end intrinsic;


intrinsic DeformationCurveSpecific(monomialCurve::SeqEnum[RngMPolElt], G::SeqEnum[RngIntElt]) -> SeqEnum[RngMPolLocElt]
	{
		Computes the deformation of the monomial curve associated to the semigroup "G" with the specific choice of equations "monomialCurve".
		Implementation based on "DeformationCurve(G::[RngIntElt])" from "SingularitiesDim2/Misc.m"
	}

	I := monomialCurve; // Choose this particular monomial curve equations
	
	// The following code is the same
	
	g := #I; R := Universe(I); ZZ := Integers();
	Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
	Ni := [0] cat [ZZ!(Ei[i] div Ei[i + 1]) : i in [1..g]];
	nB := [-Ni[i+1] * G[i+1] : i in [1..g]];

	M := EModule(R, nB); N := ideal<R | I> * M;
	J := Transpose(JacobianMatrix(I));
	T_1 := N + sub<M | [M ! m : m in RowSequence(J)]>;

	Groebner(T_1); LT := [LeadingTerm(m) : m in Basis(T_1)]; D_mu := [];
	for i in [1..g] do
		LT_i := ideal<R | [m[i] : m in LT | m[i] ne 0]>;
		M_i := [M.i * m : m in MonomialBasis(quo<R | LT_i>)];
		D_mu cat:= [m : m in M_i | WeightedDegree(m) gt 0];
	end for;

	RR := LocalPolynomialRing(RationalField(), Rank(R) + #D_mu, "lglex");
	AssignNames(~RR, ["t" cat IntegerToString(i) : i in [0..#D_mu - 1]] cat
									 ["u" cat IntegerToString(i) : i in [0..g]]);
	phi := hom<R -> RR | [RR.i : i in [#D_mu + 1..Rank(RR)]]>;
	II := [RR | phi(f) : f in I];
	for i in [1..#D_mu] do
		e_i := Column(D_mu[i]);
		II[e_i] +:= RR.i * phi(D_mu[i][e_i]);
	end for; return II;
end intrinsic;


intrinsic DeformationCurveCassou(G::SeqEnum[RngIntElt]) -> SeqEnum[RngMPolLocElt], SeqEnum[RngMPolLocElt]
	{
		Computes the deformation of the monomial curve associated to the semigroup "G" with the specific choice of equations "monomialCurve".
		Implementation based on "DeformationCurve(G::[RngIntElt])" from "SingularitiesDim2/Misc.m"
	}
	
	// G = [_beta0, ..., _betag]
	// printf "G = %o\n", G;
	//semiGroupInfo := SemiGroupInfo(G);
	//g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
	planeBranchNumbers := PlaneBranchNumbers(G);
	g, c, betas, es, ms, ns, qs, _betas, _ms, Nps, kps, Ns, ks := Explode(planeBranchNumbers);
	// printf "g = %o\n", g;
	// printf "c = %o\n", c;
	// printf "betas = %o\n", betas;
	// printf "es = %o\n", es;
	// printf "ms = %o\n", ms;
	// printf "ns = %o\n", ns;
	// printf "qs = %o\n", qs;
	// printf "_ms = %o\n", _ms;
	n := ns[2..(g+1)]; // ns = [0, n1, ..., ng], n = [n1, ..., ng]
	printf "n = %o\n", n;
	l := [];
	for s in [1..g] do
		isInG, ls := SemigroupCoordinatesCassouNogues(n[s]*G[s+1], G[(0+1)..(s-1+1)], ns);
		require isInG : Sprintf("n_%o * _beta_%o = %o not in semigroup %o\n", s, s, n[s]*G[s+1], G[(0+1)..(s-1+1)]);
		// printf "s=%o, ls=%o\n", s, ls;
		l[s] := ls[1];
		// printf "comparison %o", SemiGroupCoord(n[s]*G[s+1], G[(0+1)..(s-1+1)]);
	end for;
	printf "l =\n"; IndentPush(); printf "%o\n", l; IndentPop();
	
	// Monomial curve equations
	R := PolynomialRing(RationalField(), G);
	AssignNames(~R, ["u" cat IntegerToString(i) : i in [0..#G - 1]]);
	monomialCurve := [R| (R.(i +1))^n[i] - Monomial(R, l[i] cat [0 : j in [1..(g+1-#l[i])]]) : i in [1..g]];
	printf "monomialCurve =\n"; IndentPush(); printf "%o\n", monomialCurve; IndentPop();
	// I := monomialCurve;
	
	// intrinsic MonomialCurve(G::[RngIntElt]) -> []
	// { Computes the monomial curve associated to a semigroup of a
	// plane curve }
	// E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
	// N := [E[i - 1] div E[i] : i in [2..#G]];
	// R := PolynomialRing(RationalField(), G); I := [R | ];
	// AssignNames(~R, ["u" cat IntegerToString(i) : i in [0..#G - 1]]);
	// for i in [1..#G - 1] do
	//   // _, L_i := SemiGroupMembership(n[i] * G[i + 1], G[[1..i]]);
	//   I cat:= [R.(i + 1)^n[i] - &*[R.j^l[i][j] : j in [1..i]]];
	// end for;
	// // return I;
	// printf "I = %o\n", I;
	
	// g := #I; R := Universe(I);
	// ZZ := Integers();
	// Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]]; // = es
	// Ni := [0] cat [ZZ!(Ei[i] div Ei[i + 1]) : i in [1..g]]; // = ns
	// nB := [-Ni[i+1] * G[i+1] : i in [1..g]]; // = -Nps
	// printf "g = %o\n", g;
	// printf "R =\n"; IndentPush(); printf "%o\n", R; IndentPop();
	// printf "ZZ =\n"; IndentPush(); printf "%o\n", ZZ; IndentPop();
	// printf "Ei =\n"; IndentPush(); printf "%o\n", Ei; IndentPop();
	// printf "Ni =\n"; IndentPush(); printf "%o\n", Ni; IndentPop();
	// printf "nB =\n"; IndentPush(); printf "%o\n", nB; IndentPop();
	
	// printf "\n";
	
	minusNps := [-ns[i+1] * G[i+1] : i in [1..g]];
	M := EModule(R, minusNps);
	//M := EModule(R, nB);
	
	// printf "M =\n"; IndentPush(); printf "%o\n", M; IndentPop();
	// printf "BaseRing = %o\n", BaseRing(M);
	// // printf "rank = %o\n", Rank(M);
	// N := ideal<R | I> * M;
	// printf "N =\n"; IndentPush(); printf "%o\n", N; IndentPop();
	// J := Transpose(JacobianMatrix(I));
	// // printf "J =\n"; IndentPush(); printf "%o\n", J; IndentPop();
	// T_1 := N + sub<M | [M ! m : m in RowSequence(J)]>;
	// printf "T_1 =\n"; IndentPush(); printf "%o\n", T_1; IndentPop();
	
	// print "-----------------------------------------------------------------";
	// print M / N;
	// // printf "\n";
	
	// Groebner(T_1);
	// printf "T_1 =\n"; IndentPush(); printf "%o\n", T_1; IndentPop();
	// LT := [LeadingTerm(m) : m in Basis(T_1)];
	// // printf "LT =\n"; IndentPush(); printf "%o\n", LT; IndentPop();
	
	// // u0 := R.1;
	// // u1 := R.2;
	// // u2 := R.3;
	// // printf ">>>>>>>>>>>>>>>> %o\n", LeadingTerm(M![  3/5*u0^2,     u0*u1^3]);
	
	// // printf "\n";
	
	// D_mu := [];
	// for i in [1..g] do
	//   // printf "\n### for loop -> step %o of %o\n", i, g;
	//   LT_i := ideal<R | [m[i] : m in LT | m[i] ne 0]>;
	//   // printf "LT_i =\n"; IndentPush(); printf "%o\n", LT_i; IndentPop();
	//   M_i := [M.i * m : m in MonomialBasis(quo<R | LT_i>)];
	//   // printf "M_i =\n"; IndentPush(); printf "%o\n", M_i; IndentPop();
	//   D_mu cat:= [m : m in M_i | WeightedDegree(m) gt 0];
	//   // printf "D_mu =\n"; IndentPush(); printf "%o\n", D_mu; IndentPop();
	// end for;
	// printf "D_mu =\n"; IndentPush(); printf "%o\n", D_mu; IndentPop();
	
	// // printf "\n";
	
	// // RRRRRRRRRRRRRRRRRRRRRRRRRRRRR
	// A := quo<M | T_1>;
	// // B := quo<M | LT>;
	// // C := quo<M | D_mu>;
	// printf "quotient by T_1: A =\n"; IndentPush(); printf "%o\n", A; IndentPop();
	// // printf "quotient LT: B =\n"; IndentPush(); printf "%o\n", B; IndentPop();
	// // printf "quotient D_mu: C =\n"; IndentPush(); printf "%o\n", C; IndentPop();
	// // printf "A=B %o\n", A eq B;
	// // printf "B=C %o\n", B eq C;
	// // printf "A=C %o\n", A eq C;
	// // printf "Basis A: \n"; IndentPush(); printf "%o\n", Basis(A); IndentPop();
	// DD := sub<A | D_mu>;
	// // printf "DD =\n"; IndentPush(); printf "%o\n", DD; IndentPop();
	// // Groebner(D);
	// // printf "Groebner D =\n"; IndentPush(); printf "%o\n", D; IndentPop();
	// printf "A = DD %o\n", A eq DD;
	// printf "A > DD %o\n", DD subset A;
	// printf "A < DD %o\n", A subset DD;
	// // F := quo<A| DD>;
	// // Groebner(F);
	// // printf "A/DD =\n"; IndentPush(); printf "%o\n", F; IndentPop();
	// // printf "Rank(A/DD) = %o\n", Rank(F);
	// // F := quo<A| A>;
	// // Groebner(F);
	// // printf "A/A =\n"; IndentPush(); printf "%o\n", F; IndentPop();
	// // printf "Rank(A/A) =\n"; IndentPush(); printf "%o\n", Rank(F); IndentPop();
	// // EE := sub<M|D_mu>;
	// // E := quo<EE| T_1 >;
	// // printf "E =\n"; IndentPush(); printf "%o\n", E; IndentPop();
	// // printf "A=E %o\n", A eq E;
	// // d := #D_mu;
	// // print VectorSpace(RationalField(), d) ! A;
	// // print ChangeRing(A, RationalField());
	// //
	// // print M.1; // e1 = [1, 0, ..., 0]
	// // print R.1; // u0
	
	basisOfDeformationModule := [M| ];
	
	// Almiron,Moyano Thm2.4 (1)
	E := ExponentSetE(l, n);
	// printf "E =\n"; IndentPush(); printf "%o\n", E; IndentPop();
	// 1,2 or 2,1 ??????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????
	monomials := [ Monomial(R, [ij[1], ij[2]] cat [0 : m in [(2+1)..(g+1)]]) : ij in E ];
	// printf "monomials =\n"; IndentPush(); printf "%o\n", monomials; IndentPop();
	for m in [2..g] do
		monomials := [ mon * R.(m+1)^(km) : mon in monomials, km in [0..(n[m]-1)] ];
	end for;
	// printf "monomials =\n"; IndentPush(); printf "%o\n", monomials; IndentPop();
	basisOfDeformationModule cat:= [ mon * M.1 : mon in monomials ];
	
	// Almiron,Moyano Thm2.4 (2), (3), (4)
	for s in [2..g] do
		D := ExponentSetDlSSm1(s, l, n);
		// printf "D =\n"; IndentPush(); printf "%o\n", D; IndentPop();
		// 1,2 or 2,1 ??????????????????????????????????????????????????????????????????????????????????????????????????????????????????????????
		monomials := [ Monomial(R, [kstart[1], kstart[2]] cat kstart[3..(s-1+1)] cat [0 : m in [(s+1)..(g+1)]]) : kstart in D ];
		// printf "monomials =\n"; IndentPush(); printf "%o\n", monomials; IndentPop();
		monomials := [ mon * R.(s+1)^(ks) : mon in monomials, ks in [0..(n[s]-2)] ];
		for m in [(s+1)..g] do
			monomials := [ mon * R.(m+1)^(km) : mon in monomials, km in [0..(n[m]-1)] ];
		end for;
		// printf "monomials =\n"; IndentPush(); printf "%o\n", monomials; IndentPop();
		basisOfDeformationModule cat:= [ mon * M.s : mon in monomials ];
	end for;
	
	// printf "basisOfDeformationModule =\n";
	// for i in [1..#basisOfDeformationModule] do
	// 	elt := basisOfDeformationModule[i];
	// 	wdeg := WeightedDegree(elt);
	// 	if (wdeg gt 0) then
	// 		printf "yes    %-20o deg = %o\n", elt, wdeg;
	// 	else
	// 		printf "    no %-20o deg = %o\n", elt, wdeg;
	// 	end if;
	// end for;
	// printf "\n";
	
	// Remove non-mu-constant monomials
	basisOfMuConstantDeformation := [M| elt : elt in basisOfDeformationModule | WeightedDegree(elt) gt 0 ];
	
	// printf "ELS QUE TENEN PES =0:\n%o\n", [M| elt : elt in basisOfDeformationModule | WeightedDegree(elt) eq 0 ];

	// printf "basisOfMuConstantDeformation =\n"; IndentPush();
	// printf "%o\n", basisOfMuConstantDeformation;
	// IndentPop(); printf "\n";
	
	// Move to the front of the basis the elements necessary for being a plane curve:
	// [u2,0,...,0], ..., [0,...,0,ug,0]
	firstTerms := [M| R.(s +1) * M.(s-1) : s in [2..g]];
	for i in [1..#firstTerms] do
		Exclude(~basisOfMuConstantDeformation, firstTerms[i]);
	end for;
	basisOfMuConstantDeformation := firstTerms cat basisOfMuConstantDeformation;
	printf "firstTerms (to have plane curve) =\n"; IndentPush(); printf "%o\n", firstTerms; IndentPop();
	printf "basisOfMuConstantDeformation =\n"; IndentPush(); printf "%o\n", basisOfMuConstantDeformation; IndentPop();
	
	
	// NewModule := sub<A | basisOfDeformationModule>;
	// printf "A = NewModule %o\n", A eq NewModule;
	// printf "A < NewModule %o\n", A subset NewModule;
	// printf "A > NewModule %o\n", NewModule subset A;
	// printf "DD = NewModule %o\n", DD eq NewModule;
	// printf "DD < NewModule %o\n", DD subset NewModule;
	// printf "DD > NewModule %o\n", NewModule subset DD;
	
	// T_2 := N + sub<M | [M ! m : m in RowSequence(J)]>;
	// printf "T_2 =\n"; IndentPush(); printf "%o\n", T_2; IndentPop();
	
	// printf "basis T_2 =\n"; IndentPush(); printf "%o\n", Basis(T_2); IndentPop();
	// for b in Basis(T_2) do
	//   printf "%o = ", b;
	//   coord := Coordinates(T_1, b);
	//   // printed := false;
	//   // for i->c in coord do
	//   //   if c ne 0 then
	//   //     if printed then printf "+ "; else printed := true; end if;
	//   //     printf "%o * %o ", c, T_1.i;
	//   //   end if;
	//   // end for;
	//   // printf "\n\n";
	//   // if b ne &+[c*T_1.i : i->c in coord] then printf "ELEMENT AND COORDINATES DO NOT MATCH\n"; end if;
	//   printf "%o\n", coord;
	// end for;
	
	// print "ñññññññññññññññññññññññ";
	// TTT := quo<T_2 | Basis(sub<T_2| [M![2*R.2,-R.1^5], M![0,2*R.3]]> + ideal<R | I> * M) >;
	// // Groebner(TTT);
	// print TTT;
	
	// printf "\n";
	
	// // Testing
	
	// basisElementsOK := true;
	// for b in basisOfDeformationModule do
	//   if b in T_1 then
	//     basisElementsOK := false;
	//     printf "%-15o = 0  !!!!!\n", b; // in T1(C^Gamma)
	//     coord := Coordinates(T_1, b);
	//     // printf "coord =\n";
	//     // IndentPush();
	//     // printf "%o\n", coord;
	//     // printf "Linear comb. = %o\n", &+[c*T_1.i : i->c in coord];
	//     // IndentPop();
	//     IndentPush();
	//     printf "%o = ", b;
	//     printed := false;
	//     for i->c in coord do
	//       if c ne 0 then
	//         if printed then printf "+ "; else printed := true; end if;
	//         printf "%o * %o ", c, T_1.i;
	//       end if;
	//     end for;
	//     printf "\n\n";
	
	//     IndentPop();
	//   else
	//     printf "%-15o != 0  OK\n", b; // in T1(C^Gamma)
	//   end if;
	// end for;
	
	// printf "\n";
	// printf "basis elements OK: %o\n", basisElementsOK;
	
	// printf "\n";
	// mu := MilnorNumber(G);
	// printf "Milnor number = %o\n", mu;
	// printf "#basisOfDeformationModule = %o\n", #basisOfDeformationModule;
	
	// printf "\n";
	// printf basisElementsOK and (mu eq #basisOfDeformationModule) select "NEW BASIS OK\n" else "NEW BASIS WRONG\n";
	
	// print Degree(basisOfDeformationModule[6]);
	
	// print "------------------------------------------------------------------------";
	// Q3<a,b,c> := PolynomialRing(Rationals(),3);
	// II := ideal<Q3| a,b,c>;
	// MM := EModule(Q3, 1);
	// MI := quo<MM | II>;
	// M2 := EModule(Q3, 2);
	// M2q := quo<M2 | b*M2.1, c*M2.1, b*M2.2, c*M2.2, a^2*M2.1, a*M2.1 - a*M2.2>;
	// print MM;
	// print MI;
	// print M2q;
	// print "";
	// print Presentation(MM);
	// print Degree(Presentation(MM));
	// print Presentation(MI);
	// print Degree(Presentation(MI));
	// print Presentation(M2q);
	// print Degree(Presentation(M2q));
	// print Basis(M2q);
	// Groebner(M2q);
	// print Basis(M2q);
	// print "";
	// print MI.1;
	// m := Matrix(Q3, 2, 2, [Q3| 1, 0, 0, 1 ]);
	// print m;
	// MMM := DirectSum([* MM, MM *]);
	// print MMM;
	// print "kkkkkkkkkkkkkkkkkkkkkkk";
	// h := Homomorphism(MMM, M2q, m);
	// print h;
	// print "kkkkkkkkkkkkkkkkkkkkkkk";
	// // print h(MMM.1);
	// // print h(MMM.2 * (b+1)*c^2);
	// print "Ker(h) =",Kernel(h);
	// // print h(MMM.3);
	// printf "\n";
	
	D_mu := basisOfMuConstantDeformation;
	// printf "Universe(D_mu) = %o\n", Universe(D_mu);
	
	RR := LocalPolynomialRing(RationalField(), Rank(R) + #D_mu, "lglex");
	AssignNames(~RR, ["t" cat IntegerToString(i) : i in [0..#D_mu - 1]] cat
	                 ["u" cat IntegerToString(i) : i in [0..g]]);
	printf "RR =\n"; IndentPush(); printf "%o\n", RR; IndentPop();
	phi := hom<R -> RR | [RR.i : i in [#D_mu + 1..Rank(RR)]]>; // convert from Q[u] to Q[t,u]
	// printf "phi =\n"; IndentPush(); printf "%o\n", phi; IndentPop();
	
	// Add deformation terms to the monomial curve
	monomialCurve := [RR | phi(f) : f in monomialCurve];
	deformedMonomialCurve := monomialCurve;
	// printf "deformedMonomialCurve =\n"; IndentPush(); printf "%o\n", deformedMonomialCurve; IndentPop();
	// printf "\n";
	for i in [1..#D_mu] do
		e_i := Column(D_mu[i]); // Position of the monomial in the "vector"
		deformedMonomialCurve[e_i] +:= RR.i * phi(D_mu[i][e_i]);
		// printf "\n### for loop -> step %o of %o\n", i, #D_mu;
		// printf "e_i =\n"; IndentPush(); printf "%o\n", e_i; IndentPop();
		// printf "deformedMonomialCurve =\n"; IndentPush(); printf "%o\n", deformedMonomialCurve; IndentPop();
	end for;
	printf "monomialCurve =\n"; IndentPush(); printf "%o\n", monomialCurve; IndentPop();
	printf "deformedMonomialCurve =\n"; IndentPush(); printf "%o\n", deformedMonomialCurve; IndentPop();
	return monomialCurve, deformedMonomialCurve;
end intrinsic;








