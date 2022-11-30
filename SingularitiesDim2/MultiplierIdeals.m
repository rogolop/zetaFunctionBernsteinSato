import "ProximityMatrix.m": ProximityMatrixImpl;
import "IntegralClosure.m": IntegralClosureIrreducible, Unloading, ProductIdeals,
                            ClusterFactorization;

// Reference: Naie - "Jumping numbers of a unibranch curve on a smooth surface"
intrinsic JumpingNumbers(G::[RngIntElt]) -> []
{ Compute the Jumping Numbers < 1 of an irreducible plane curve
  from its semigroup }
require IsPlaneCurveSemiGroup(G): "G must be the semigroup of a plane curve";

  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  RSet := func<p, q | [a*p+b*q : a in [1..q], b in [1..p] | a*p+b*q lt p*q]>;

  g := #G - 1; JN := [];
  for i in [1..g] do
    p := E[i] / E[i + 1]; q := G[i + 1] / E[i + 1]; R := RSet(p, q);
    Rmj := [k*p*q + alpha : k in [0..E[i+1] - 1], alpha in R];
    JN cat:= [[beta / Lcm(E[i], G[i + 1]) : beta in Sort(Rmj)]];
  end for; return JN;
end intrinsic;

// Reference: Naie - "Jumping numbers of a unibranch curve on a smooth surface"
intrinsic JumpingNumbers(n::RngIntElt, M::[RngIntElt]) -> []
{ Compute the Jumping Numbers < 1 of an irreducible plane curve from its
  char. exponents }

  G := SemiGroup(n, M); return JumpingNumbers(G);
end intrinsic;

intrinsic MultiplierIdeals(f::RngMPolLocElt : MaxJN := 1) -> []
{ Computes the Multiplier Ideals and its associated Jumping Number for an
  plane curve in a smooth complex surface using the algorithm
  of Alberich-Alvarez-Dachs }

  // With the extra point there is no confusion whether and affine component
  // has multiplicity or not.
  P, E, C := ProximityMatrix(f: Coefficients := true, ExtraPoint := true); QQ := Rationals();
  EQ := ChangeRing(E, QQ); PQ := ChangeRing(P, QQ); PQTinv := Transpose(PQ)^-1;
  n := Ncols(P); F := EQ*PQTinv; K := Matrix([[QQ | 1 : i in [1..n]]]);
  // Compute relative canonical divisor.
  K := K*PQTinv; ZZ := Integers(); k := Parent(f);

  // Compute the extended intersection matrix by the stict transform components.
  N := Transpose(PQ)*PQ; StrF := EQ*PQ;
  nAffComp := #[1 : i in [1..n] | StrF[1][i] ne 0];
  N := DiagonalJoin(N, -IdentityMatrix(QQ, nAffComp));
  idxAff := [i : i in [1..n] | StrF[1][i] ne 0];
  for i in [1..nAffComp] do N[n + i][idxAff[i]] := -1; end for;
  F := HorizontalJoin(F, Matrix(QQ, [[1 : i in [1..nAffComp]]]));
  K := HorizontalJoin(K, Matrix(QQ, [[0 : i in [1..nAffComp]]]));

  JN := 0; S := [];
  while JN lt MaxJN do
    D := Unloading(N, Matrix([[QQ | Floor(ei) : ei in Eltseq(JN*F - K)]]));
    lastJN := JN; JN, i := Min([(K[1][i] + 1 + D[1][i])/F[1][i] : i in [1..n]]);
    DZZ := ColumnSubmatrix(ChangeRing(D, ZZ), n);
    S cat:= [<GeneratorsOXD(P, DZZ, C, k), lastJN>];
  end while; return S;
end intrinsic;

intrinsic MultiplierIdeals(I::RngMPolLoc : MaxJN := 1) -> []
{ Computes the Multiplier Ideals and its associated Jumping Number for an
  m-primary ideal in a smooth complex surface using the algorithm
  of Alberich-Alvarez-Dachs }
// TODO: Fix this requiriment. This would involve getting the proximity matrix
// of a non m-primary ideal. This means merging the affine part resolution.
require Gcd(Basis(I)) eq 1: "Ideal must be m-primary";

  P, F, _, C := LogResolution(I: Coefficients := true); QQ := Rationals();
  F := ChangeRing(Matrix(F), QQ); PQ := ChangeRing(P, QQ); ZZ := Integers();
  PQTinv := Transpose(PQ)^-1; k := Universe(Basis(I)); n := Ncols(P);
  // Compute relative canonical divisor.
  K := Matrix([[QQ | 1 : i in [1..n]]]); K := K*PQTinv;
  // Compute the intersection matrix
  N := Transpose(PQ)*PQ;

  JN := 0; S := [];
  while JN lt MaxJN do
    D := Unloading(N, Matrix([[QQ | Floor(ei) : ei in Eltseq(JN*F - K)]]));
    lastJN := JN;
    JN, i := Min([(K[1][i] + 1 + D[1][i])/F[1][i] : i in [1..n]]);
    S cat:= [<GeneratorsOXD(P, ChangeRing(D, ZZ), C, k), lastJN>];
  end while; return S;
end intrinsic;

intrinsic AdjointIdeal(f::RngMPolLocElt) -> []
{ Computes the adjoint ideal of a plane curve }
  P, E, C := ProximityMatrix(f: Coefficients := true); QQ := Rationals();
  EQ := ChangeRing(E, QQ); PQ := ChangeRing(P, QQ); PQTinv := Transpose(PQ)^-1;
  n := Ncols(P); F := EQ*PQTinv; K := Matrix([[QQ | 1 : i in [1..n]]]);
  // Compute relative canonical divisor.
  K := K*PQTinv; ZZ := Integers(); k := Parent(f);
  // Compute the intersection matrix.
  N := Transpose(PQ)*PQ;

  JN := 1; S := [];
  D := Unloading(N, Matrix([[QQ | Floor(ei) : ei in Eltseq(JN*F - K)]]));
  return GeneratorsOXD(P, ChangeRing(D, ZZ), C, k);
end intrinsic;

intrinsic TopologicalRootsBS(G::[RngIntElt]) -> []
{ Compute the topological roots of the Bernstein-Sato polynomial of a
  topological class given by the semigroup G }

  P, E := ProximityMatrix(G); QQ := Rationals(); ZZ := Integers();
  n := Ncols(P); P := ChangeRing(P, QQ); Pt := Transpose(P);
  E := ChangeRing(E, QQ); PTinv := Pt^-1; F := E*PTinv;
  K := Matrix([[QQ | 1 : i in [1..n]]]); K := K*PTinv; N := Pt*P;

  VS := RSpace(ZZ, n); R := []; isSat := &+[VS | Pt[i] : i in [1..n]];
  for p in [2..n] do // Construct the set of rupture points.
    // Points proximate to 'p' that are free.
    prox_p_free := [i : i in [p + 1..n] | Pt[p][i] eq -1 and isSat[i] ne -1];
    if (isSat[p] eq -1 and (#prox_p_free ge 1)) then R cat:= [p]; end if;
  end for; R cat:= [n];

  JN := [];
  Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  for i in [1..# G - 1] do
    JNi := 0; Si := []; r := R[i]; lct := (K[1][r] + 1)/F[1][r];
    Fi := Matrix([[QQ | 0 : j in [1..n]]]); Fi[1][r] := F[1][r];
    while JNi lt 1 + lct do
      D := Unloading(N, Matrix([[QQ | Floor(ei) : ei in Eltseq(JNi*Fi - K)]]));
      JNi := (K[1][r] + 1 + D[1][r])/F[1][r];
      if Denominator(Ei[i]*JNi) ne 1 and Denominator(G[i + 1]*JNi) ne 1 then
        Si cat:= [JNi];
      end if;
    end while; JN cat:= [Si[1..#Si - 1]];
  end for; return JN;
end intrinsic;
