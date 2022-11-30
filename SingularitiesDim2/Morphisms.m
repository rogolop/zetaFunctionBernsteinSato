intrinsic PuiseuxTrunk(F::[RngMPolLocElt]) -> []
{ Compute the Puiseux expansion associated to a map F }
require Rank(Universe(F)) eq 2: "Argument must be bivariate polynomials";
  A<a> := LaurentSeriesRing(AlgebraicClosure(RationalField()));
  P<t> := PuiseuxSeriesRing(A);
  S := [P | Evaluate(f, <t, a*t>) : f in F];
  Sort(~S, func<x, y | Valuation(x) - Valuation(y)>);
  n := Valuation(S[1]); tt := Reverse(S[1]^(1/n));
  return [P | t^n] cat [P | Evaluate(S[i], tt) : i in [2..#S]];
end intrinsic;

intrinsic Multiplicity(f::RngMPolLocElt) -> RngIntElt
{ Compute the multiplicity at the origin of an hypersurface singularity }
  R := Parent(f); M := ideal<R | R.1, R.2>; n := 0; I := M;
  while NormalForm(f, I) eq 0 do
    I *:= M; n +:= 1;
  end while; return n;
end intrinsic;

intrinsic TangentCone(f::RngMPolLocElt) -> RngMPolLocElt
{ Computes the tangent cone at the origin of an hypersuface }
  n := Multiplicity(f);
  return &+[m : m in Terms(f) | TotalDegree(m) eq n];
end intrinsic;

intrinsic Trunk(F::[RngMPolLocElt]) -> []
{ Compute the pencil associated to the trunk of the morphism F }
require Rank(Universe(F)) eq 2: "Argument must be bivariate polynomials";
require #F eq 2: "Morphism must be defined by two elements";
  R := Parent(F[1]); S<u, v> := LocalPolynomialRing(RationalField(), 2);
  Sort(~F, func<x, y | Multiplicity(x) - Multiplicity(y)>);
  n := Min([Multiplicity(f) : f in F]); H := [u, v]; G := [n];
  N := [n]; Phi := hom<S -> R | F>; h0 := TangentCone(Phi(u));

  h := TangentCone(Phi(H[#H])); m := Multiplicity(Phi(H[#H]));
  while Determinant(JacobianMatrix([h, h0])) eq 0 do
    G cat:= [m]; ni := Gcd(N[#N], m); N cat:= [ni];
    nn := N[#N - 1] div N[#N]; _, v := SemiGroupMembership(nn * m, G);
    Q := &*[H[i]^v[i] : i in [1..#G]]; q := TangentCone(Phi(Q));
    a := S!ExactQuotient(q^m, h^(nn * m)); H cat:= [H[#H]^nn - a * Q];
    h := TangentCone(Phi(H[#H])); m := Multiplicity(Phi(H[#H]));
  end while;

  G cat:= [m]; ni := Gcd(N[#N], m); N cat:= [ni];
  nn := N[#N - 1] div N[#N]; _, v := SemiGroupMembership(nn * m, G);
  return [H[#H], &*[H[i]^v[i] : i in [1..#G]]], G, nn;
end intrinsic;

intrinsic TangentMap(F::[RngMPolLocElt]) -> []
{ The tangent map of a planar morphism }
require Rank(Universe(F)) eq 2: "Argument must be bivariate polynomials";
require #F eq 2: "Morphism must be defined by two elements";
  R := Parent(F[1]); S<u, v> := LocalPolynomialRing(RationalField(), 2);
  Sort(~F, func<x, y | Multiplicity(x) - Multiplicity(y)>);
  T := Trunk(F); Phi := hom<S -> R | F>; T := [Phi(S!g) : g in T];
  return [TangentCone(g) : g in T];
end intrinsic;
