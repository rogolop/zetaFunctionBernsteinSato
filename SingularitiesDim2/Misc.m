import "ProximityMatrix.m": ProximityMatrixImpl;
import "SemiGroup.m": Euclides;

intrinsic MonomialCurve(G::[RngIntElt]) -> []
{ Computes the monomial curve assocaited to a semigroup of a
  plane curve }
require IsPlaneCurveSemiGroup(G): "G is not the semigroup of a plane curve";

  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]];

  R := PolynomialRing(RationalField(), G); I := [R | ];
  AssignNames(~R, ["u" cat IntegerToString(i) : i in [0..#G - 1]]);
  for i in [1..#G - 1] do
    _, L_i := SemiGroupMembership(N[i] * G[i + 1], G[[1..i]]);
    I cat:= [R.(i + 1)^N[i] - &*[R.j^L_i[j] : j in [1..i]]];
  end for; return I;
end intrinsic;

intrinsic MonomialCurve(n::RngIntElt, M::[RngIntElt]) -> []
{ Computes the monomial curve associated to a characteristic sequence }

  G := SemiGroup(n, M);
  return MonomialCurve(G);
end intrinsic;

intrinsic DeformationCurve(G::[RngIntElt]) -> []
{ Computes the deformations of the monomial curve associated to the
  semigroup G }

  I := MonomialCurve(G); g := #I; R := Universe(I); ZZ := Integers();
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

intrinsic ESufficiencyDegree(f::RngMPolLocElt) -> RngIntElt
{ Computes the E-sufficiency degree of a plane curve }
require Evaluate(f, <0, 0>) eq 0: "Curve must be non-empty";

  branches := PuiseuxExpansion(f); P, E, _ := ProximityMatrixImpl(branches);
  ZZ := IntegerRing(); VS := RSpace(ZZ, Ncols(P));

require &+[ZZ | Gcd(Eltseq(e)) : e in E] eq #E: "Curve must be reduced";

  Pt := Transpose(P); N := Ncols(P); isSat := &+[VS | Pt[i] : i in [1..N]];
  // Construct subset T of free points of K.
  freePoints := [p : p in [1..N] | isSat[p] eq 0]; T := []; exc := &+E*P;
  for p in freePoints do
    // Points proximate to 'p'.
    prox_p := [i : i in [p + 1..N] | Pt[p][i] eq -1];
    // Points proximate to 'p' that are satellites.
    prox_p_sat := [q : q in prox_p | isSat[q] eq -1];
    // Select 'p' if all its proximate points in K are
    // satellite and its excess is equal to 1.
    if #prox_p eq #prox_p_sat and exc[1][p] eq 1 then T cat:= [p]; end if;
  end for;
  // Apply theorem 7.5.1 (Casas-Alvero)
  QQ<n> := PolynomialRing(RationalField()); Pt := ChangeRing(Pt, QQ);
  e := ChangeRing(&+E, QQ); i_O := ZeroMatrix(QQ, 1, N); i_O[1][1] := 1;
  u := (i_O*n - e)*Pt^-1; ns := [ZZ | ];
  for p in [1..N] do
    a := Roots(u[1][p])[1][1]; b := Ceiling(a);
    ns cat:= [p in T select b else (a eq b select a + 1 else b)];
  end for; E := Max(ns); return E;
end intrinsic

intrinsic PolarInvariants(f::RngMPolLocElt) -> []
{ Computes the polar invariants of a plane curve }
require Evaluate(f, <0, 0>) eq 0: "Curve must be non-empty";

  branches := PuiseuxExpansion(f); P, E, _ := ProximityMatrixImpl(branches);
  ZZ := IntegerRing(); VS := RSpace(ZZ, Ncols(P));

require &+[ZZ | Gcd(Eltseq(e)) : e in E] eq #E: "Curve must be reduced";

  Pt := Transpose(P); N := Ncols(P); isSat := &+[VS | Pt[i] : i in [1..N]];
  Pinv := P^-1; e := Transpose(&+E); exc := Pt*e; R := [1];
  for p in [2..N] do // Construct the set of rupture points.
    // Points proximate to 'p' that are free.
    prox_p_free := [i : i in [p + 1..N] | Pt[p][i] eq -1 and isSat[i] ne -1];
    if (isSat[p] eq -1 and (#prox_p_free ge 1 or exc[p][1] gt 0)) or
       (isSat[p] ne -1 and #prox_p_free ge 2) then R cat:= [p]; end if;
  end for; I := [];
  // For each rupture point compute the polar invariant.
  for p in R do
    i_p := ZeroMatrix(ZZ, 1, N); i_p[1][p] := 1;
    e_p := i_p*Pinv; I cat:= [(e_p*e)[1][1] / e_p[1][1]];
  end for; return I;
end intrinsic;

intrinsic ASufficiencyBound(f::RngMPolLocElt) -> RngIntElt
{ Computes a lower-bound for the A-sufficiency degree of a plane curve }

  I := PolarInvariants(f);
  a := 2*Max(I); b := Ceiling(a);
  return a eq b select a + 1 else b;
end intrinsic;

intrinsic Spectrum(G::[RngIntElt]) -> []
{ The singularity spectrum of an irreducible plane curve singularity }
require IsPlaneCurveSemiGroup(G): "G is not the semigroup of a plane curve";

  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]]; g := #G - 1; n := G[1]; S := [];

  for i in [1..#G - 1] do
    Mi := G[i+1] div E[i+1];
    S cat:= [(Mi*j + N[i]*k + r*N[i]*Mi)/(N[i]*G[i+1]) :
      j in [1..N[i] - 1], k in [1..Mi - 1], r in [0..E[i+1] - 1] |
        Mi*j + N[i]*k lt N[i]*Mi];
  end for; return S cat [2 - s : s in S];
end intrinsic;

intrinsic Spectrum(f::RngMPolLocElt) -> []
{ The singularity spectrum of an irreducible plane curve singularity }

  return Spectrum(SemiGroup(f));
end intrinsic;

intrinsic BExponents(n::RngIntElt, M::[RngIntElt]) -> RngSerPuisElt
{ Computes the generating sequence for the generic b-exponents
  from the characteristic sequence using Yano's formula }

  G := SemiGroup(n, M); M := [n] cat M;
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];

  Rk := [i gt 1 select (E[i - 1] div E[i]) * (Self(i - 1) + M[i] - M[i - 1])
    else n : i in [1..#G]];
  rk := [(M[i] + n) div E[i] : i in [1..#G]];
  Rk_ := [n] cat [(Rk[i] * E[i]) div E[i - 1] : i in [2..#G]];
  rk_ := [2] cat [(rk[i] * E[i]) div E[i - 1] + 1 : i in [2..#G]];

  P<t> := PuiseuxSeriesRing(RationalField());
  s := &+[P | t^(rk[i]/Rk[i]) * (1 - t)/(1 - t^(1/Rk[i])) : i in [2..#Rk]] -
        &+[P | t^(rk_[i]/Rk_[i]) * (1 - t)/(1 - t^(1/Rk_[i])) :
          i in [1..#Rk_]] + t;
  return ChangePrecision(s, Infinity());
end intrinsic;

intrinsic BExponents(G::[RngIntElt]) -> RngSetPuisElt
{ Computes the generating sequence for the generic b-exponents
  from the semigroup using Yano's formula }

    C := CharExponents(G); n := C[1][2]; C := [C[i][1] : i in [2..#C]];
    return BExponents(n, C);
end intrinsic;
