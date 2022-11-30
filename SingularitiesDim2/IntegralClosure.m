import "SemiGroup.m": Euclides, TailExponentMatrix, InversionFormula;

// Given a Puiseux series s, returns its associated Weierstrass equation.
intrinsic WeierstrassEquation(s::RngSerPuisElt, Q::RngMPolLoc) ->
  RngMPolLocElt
{ Computes the Weierstrass equation associated to a Puiseux series }

  x := Q.1; y := Q.2; C, m, n := Coefficients(s); G := CyclicGroup(n);
  g := n gt 1 select G.1^(n - 1) else G.0;

  V := [&+[Q | C[i + 1] * x^((m + i - s) div n) : i in [0..#C - 1] |
    (i + m) mod n eq s] : s in [0..n - 1]];
  M := Matrix([V[Eltseq(g^i)] : i in [0..n - 1]]);
  for i in [1..n] do
    InsertBlock(~M, x * Submatrix(M, [i], [1..i - 1]), i, 1);
  end for;
  return Determinant(ScalarMatrix(n, y) - M);
end intrinsic;

// Factorices the weighted cluster (P, v) as a unique sum of
// irreducible weighted clusters.
ClusterFactorization := function(P, v)
  N := Transpose(P) * P; Ninv := N^-1; exc := v * N; n := Ncols(P);
  B := []; // For each point with strictly positive excess.
  for i in [i : i in [1..n] | exc[1][i] gt 0] do
    p := i; I := [p];
    while p ne 1 do // Traverse the cluster back to the origin
      p := [j : j in Reverse([1..n]) | P[p][j] eq -1][1]; I := [p] cat I;
    end while;
    v := ZeroMatrix(IntegerRing(), 1, n); v[1][i] := exc[1][i];
    v := v * Ninv; B cat:= [v];
  end for; return B;
end function;

// Returns the curve going sharply through (P, v).
// Prerequisite: The cluster (P, v, c) must be irreducible.
// && the last point of (P, v) must be free.
SharplyCurve := function(P, v, c, Q)
  m := Gcd(Eltseq(v)); v := v div m; G := SemiGroup(P);
  M := CharExponents(G) cat [TailExponentMatrix(P)];
  // If the curve is the y-axis.
  if #G eq 1 and #c gt 1 and &and[c[i][1] eq 0: i in [2..#c]] then
  return Q.1; end if;
  // If the curve is inverted.
  if c[2][1] eq 0 then M := InversionFormula(M, P, c); end if;
  P<t> := PuiseuxSeriesRing(Parent(c[1][2])); s := P!0; k := 1; n := M[1][2];
  for i in [2..#M] do
    mj := M[i - 1][1]; nj := M[i - 1][2]; mi := M[i][1]; h0 := (mi - mj) div nj;
    s +:= &+[P | c[k + l][2] * t^((mj + l * nj) / n) : l in [0..h0]];
    k +:= &+Euclides(mi - mj, nj)[1];
  end for; return WeierstrassEquation(s, Q)^m;
end function;

// Computes the maximal contact elements of a weighted cluster.
MaxContactElements := function(P, v, c, Q)
  P_inv := P^-1; Pt := Transpose(P); Pt_inv := Transpose(P_inv);
  n := Ncols(P); isSat := &+[Pt[i] : i in [1..n]];
  // Dead-end points are always free.
  freePoints := [p : p in [1..n] | isSat[p] eq 0]; curvPoints := [];
  for p in freePoints do
    // Points proximate to 'p'.
    prox_p := [i : i in [p + 1..n] | Pt[p][i] eq -1];
    // Points proximate to 'p' that are satellites.
    prox_p_sat := [q : q in prox_p | isSat[q] eq -1];
    // Select 'p' is if it has no proximate points in K (dead end) or
    // all its proximate points in K are satellite (rupture point).
    if #prox_p eq 0 or #prox_p eq #prox_p_sat then
      curvPoints cat:= [p]; end if;
  end for; C := []; // Now, construct equations for each max. cont. elem.
  for p in curvPoints do
    i_p := ZeroMatrix(IntegerRing(), 1, n); i_p[1][p] := 1;
    e_p := i_p*P_inv; Ip := [i : i in [1..n] | e_p[1][i] ne 0];
    v_p := e_p*Pt_inv; f_p := SharplyCurve(Submatrix(P, Ip, Ip),
      Submatrix(v_p, [1], Ip), c[Ip], Q);
    C cat:= [<[<f_p, 1>], v_p, e_p>];
  end for;
  // Let's check if we need to add x or y as a max. cont. elem. This will always
  // happen in the irreducible case. Otherwise, we might have smooth max. cont.
  // elem. playing the role of x and/or y.
  e_O := ZeroMatrix(IntegerRing(), 1, n); e_O[1][1] := 1; v_O := e_O*Pt_inv;
  if #[f : f in C | LeadingMonomial(f[1][1][1]) eq Q.1] eq 0 then
    C := [<[<Q.1, 1>], v_O, e_O>] cat C; end if;
  if #[f : f in C | LeadingMonomial(f[1][1][1]) eq Q.2] eq 0 then
    C := [<[<Q.2, 1>], v_O, e_O>] cat C; end if;
  return C;
end function;

// Unloads the weighted cluster represented by (P, v) where v are virtual values.
Unloading := function(N, v)
  n := Ncols(N); R := CoefficientRing(N);
  while #[r : r in Eltseq(v * N) | r lt 0] gt 0 do
    p := [i : i in [1..n] | (v * N)[1][i] lt 0][1];
    lp := ZeroMatrix(R, 1, n); lp[1][p] := 1;
    rp := (lp * N * Transpose(lp))[1][1];
    np := Ceiling(-(v * N * Transpose(lp))[1][1] / rp);
    v +:= np * lp;
  end while; return v;
end function;

// Returns the datum corresponding to multipling the datum of the
// max. contact elements of f and g.
ProductMaxContElem := function(f, g)
  fg := f[1] cat g[1]; S := {h[1] : h in fg};
  return <[<s, &+[h[2] : h in fg | h[1] eq s]> : s in S],
    f[2] + g[2], f[3] + g[3]>;
end function;

// Returns the datum corresponding to raising the datum representing
// the max. cont. elem. f to alpha \in \mathbb{N}.
PowerMaxContElem := function(f, alpha)
  return <[<f_i[1], alpha * f_i[2]> : f_i in f[1]], alpha * f[2], alpha * f[3]>;
end function;

// Multiplies together all the 'ideals' of max. cont. elem. in the sequence S.
ProductIdeals := function(S)
if #S eq 0 then return []; end if;
return Reverse([i gt 1 select SetToSequence({ProductMaxContElem(f, g) :
    f in S[i], g in Self(i - 1)}) else S[1] : i in [1..#S]])[1];
end function;

// Raises the 'ideal' of max. cont. elem. to the alpha-th power.
PowerIdeal := function(I, alpha)
  return Reverse([i gt 1 select ProductIdeals([I] cat [Self(i - 1)])
    else I : i in [1..alpha]])[1];
end function;

forward IntegralClosureIrreducible;

IntegralClosureIrreducible := function(P, e, v_i, Cv, max, Q)
  // If the cluster is a power of the maximal ideal, select all the
  // possible generators for a maximal ideal from the max. cont. elem.
  alpha := Gcd(Eltseq(v_i)); v_i := v_i div alpha;
  if v_i eq max then
    X := [f : f in Cv | LeadingMonomial(f[1][1][1]) eq Q.1];
    Y := [f : f in Cv | LeadingMonomial(f[1][1][1]) eq Q.2];
    _, i1 := Max([(f[3] * e)[1][1] : f in X]);
    _, i2 := Max([(f[3] * e)[1][1] : f in Y]);
    return PowerIdeal([X[i1], Y[i2]], alpha);
  end if;

  // Find the max. cont. elem. going through the current cluster.
  Pt := Transpose(P); n := Ncols(P); isFree := &+[Pt[i] : i in [1..n]];
  e_i := v_i*Pt; p := [j : j in Reverse([1..n]) | isFree[j] eq 0 and
    e_i[1][j] ne 0][1]; // Last free point.
  Fs := [f : f in Cv | f[3][1][p] gt 0 and f[3][1][1] le v_i[1][1]][1];
  beta := v_i[1][1] div Fs[3][1][1]; N := Pt*P;

  // Increase the value at the origin & unload.
  v := v_i; v[1][1] +:= 1; v := Unloading(N, v);
  // Apply Zariski theorem on complete ideals and recurse.
  Is := [IntegralClosureIrreducible(P, e, v_j, Cv, max, Q) :
    v_j in ClusterFactorization(P, v)];

  // Compute (f^\beta) + \prod_{i=1}^{#II} I_i and clean gens.
  return PowerIdeal([PowerMaxContElem(Fs, beta)] cat [g : g in ProductIdeals(Is)
    | &or[g[2][1][i] lt (v_i + max)[1][i] : i in [1..n]]], alpha);
end function;

intrinsic IntegralClosure(I::RngMPolLoc : Ideal := true) -> []
{ Computes the integral closure of a bivariate polynomial ideal }
  // Compute the log-resolution of I
  P, v, f, c := LogResolution(I : Coefficients := true);
  Pt := Transpose(P); n := Ncols(P); R := Parent(f);
  // If the ideal is principal its integral closure is itself.
  if n eq 0 then
    if Ideal then return ideal<R | f>; else return [[<R!f, 1>]]; end if;
  end if;

  // Compute the maximal contact elements of the log-resolution morphism.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := MaxContactElements(P, v, c, Q); e := P*Transpose(v);
  // Sort max. contact elements by increasing intersection mult. with F_\pi.
  Sort(~Cv, func<x, y | (y[3]*e - x[3]*e)[1][1]>);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, n); max[1][1] := 1; max := max*Pt^-1;

  // Compute systems of generators of irreducible cluster.
  Is := [IntegralClosureIrreducible(P, P*Transpose(v_i), v_i, Cv, max, Q) :
    v_i in ClusterFactorization(P, v)];
  // Multiply all the ideals together, add the affine part and clean gens.
  Ibar := [g[1] cat (f eq 1 select [] else [<Q!f, 1>]) : g in ProductIdeals(Is)
    | &or[g[2][1][i] lt (v + max)[1][i] : i in [1..n]]];

  // Return the internal representation of the monomials in the max. contact
  // elements or return a sequence of ideals instead.
  ConvertToIdeal := func<I, Q | [Q!(&*[g[1]^g[2] : g in f]) : f in I]>;
  if Ideal then return ConvertToIdeal(Ibar, R); else return Ibar; end if;
end intrinsic;

// Computes a set of maximal contact elements of an element f.
intrinsic MaxContactElements(f::RngMPolLocElt) -> []
{ Computes a set of maximal contact elements of a plane curve f }

  P, e, c := ProximityMatrix(f : Coefficients := true); R := Parent(f);
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2); Pt := Transpose(P);
  return [R!fi[1][1][1] : fi in MaxContactElements(P, e*Pt^-1, c, Q)];
end intrinsic;

// Computes generators for \pi^* O_{X'}(-D)_O
intrinsic GeneratorsOXD(P::Mtrx, v::Mtrx, c::SeqEnum[Tup], R::RngMPolLoc) -> []
{ Computes monomial generators for the stalk at zero of the ideal
  associated to the divisor D given by the values in v}
require Ncols(P) eq Ncols(v) and Ncols(P) eq #c: "Dimensions do not agree";

  // Compute the maximal contact elements of the morphism.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := MaxContactElements(P, v, c, Q); e := P*Transpose(v);
  // Sort max. contact elements by increasing intersection multiplicity with D.
  Sort(~Cv, func<x, y | (y[3]*e - x[3]*e)[1][1]>); n := Ncols(P);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, n); max[1][1] := 1;
  max := max*Transpose(P)^-1;

  // Compute systems of generators of irreducible cluster.
  Is := [IntegralClosureIrreducible(P, P*Transpose(v_i), v_i, Cv, max, Q) :
    v_i in ClusterFactorization(P, v)];
  // Multiply all the ideals together, add the affine part and clean gens.
  Ibar := [g[1] : g in ProductIdeals(Is) | &or[g[2][1][i] lt
    (v + max)[1][i] : i in [1..n]]];

  ConvertToIdeal := func<I, Q | [Q!(&*[g[1]^g[2] : g in f]) : f in I]>;
  return ConvertToIdeal(Ibar, R);
end intrinsic;
