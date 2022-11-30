
// MilnorNumber not available for local polynomial rings.
intrinsic MilnorNumber(f::RngMPolLocElt) -> RngIntElt
{ The Milnor number of f }
  R := Parent(f); J := JacobianIdeal(f); RJ := R/J;
  if HasFiniteDimension(RJ) then return Dimension(RJ);
  else return Infinity(); end if;
end intrinsic;

// The Milnor number of the singularity defined by a plane curve semigroup.
intrinsic MilnorNumber(G::[RngIntElt]) -> RngIntElt
{ The Milnor number of a semigroup }
require IsPlaneCurveSemiGroup(G): "Argument must be a plane curve semigroup";

  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]]; g := #G - 1; n := G[1];
  return &+[(N[i] - 1) * G[i + 1] : i in [1..g]] - n + 1;
end intrinsic;

// The Milnor number of the singularity defined by a plane curve char. seq.
intrinsic MilnorNumber(n::RngIntElt, M::[RngIntElt]) -> RngIntElt
{ The Milnor number of a characteristic sequence }
  G := SemiGroup(n, M); return MilnorNumber(G);
end intrinsic;

// TjurinaNumber not available for local polynomial rings.
intrinsic TjurinaNumber(f::RngMPolLocElt) -> RngIntElt
{ The Tjurina number of f }
  R := Parent(f); Jf := JacobianIdeal(f) + ideal<R | f>; RJf := R/Jf;
  if HasFiniteDimension(RJf) then return Dimension(RJf);
  else return Infinity(); end if;
end intrinsic;

// A monomial basis for the finite dimension algebra R/(J(f) + f)
intrinsic TjurinaAlgebra(f::RngMPolLocElt) -> []
{ Monomial basis for the Tjurina algebra }
  tau := TjurinaNumber(f); R := Parent(f); g := Rank(R);
require tau ne Infinity(): "Argument must be an isolated singularity.";

  Jf := JacobianIdeal(f) + ideal<R | f>; RJf := R/Jf;
  F := hom<RJf -> R | [R.i : i in [1..g]]>;
  return Reverse(Setseq(F(MonomialBasis(RJf))));
end intrinsic;

// A monomial basis for the finite dimension algebra R/J(f)
intrinsic MilnorAlgebra(f::RngMPolLocElt) -> []
{ Monomial basis for the Milnor algebra }
  mu := MilnorNumber(f); R := Parent(f); g := Rank(R);
require mu ne Infinity(): "Argument must be an isolated singularity.";

  J := JacobianIdeal(f); RJ := R/J; F := hom<RJ -> R | [R.i : i in [1..g]]>;
  return Reverse(Setseq(F(MonomialBasis(RJ))));
end intrinsic;

// By the Briancon-Skoda theorem, for every every hypersurface defining
// an isolated singularity there exists a minimal kappa such that
// f^kappa belong to the Jacobian ideal.
intrinsic JacobianPower(f::RngMPolLocElt) -> RngIntElt
{ Computes the minimal kappa s.t. f^kappa \in J(f), f an isolated singularity }
  mu := MilnorNumber(f);
require mu ne Infinity(): "Argument must be an isolated singularity.";

  J := JacobianIdeal(f); kappa := 1;
  while NormalForm(f^kappa, J) ne 0 do kappa +:= 1; end while;
  return kappa;
end intrinsic;

// The gaps in the Tjurina filtration of the curve.
intrinsic TjurinaGaps(f::RngMPolLocElt) -> []
{ The gaps of the Tjurina ideal of an irreducible plane curve }
  R := Parent(f); g := Rank(R); tau := TjurinaNumber(f);
require tau ne Infinity(): "Argument must be an isolated singularity.";

  M := CharExponents(f); n := M[1][2]; M := [m[1] : m in M[2..#M]];
  G := SemiGroup(n, M); c := Conductor(G);

  // Elements nu < c + min(n, m1) - 1 s.t nu \in Gamma.
  Nu1 := [i : i in [0..(c + Min(n, M[1]) - 1) - 1] | SemiGroupMembership(i, G)];
  FJf := TjurinaFiltration(f); // i is a gap iff FJf[i] eq FJf[i+1].
  Nu2 := [i - 1 + (c + Min(n, M[1]) - 1) : i in [1..#FJf-1]
    | FJf[i][1] eq FJf[i+1][1]]; return Nu1, Nu2;
end intrinsic;

// An special adapted basis for the finite dimension algebra R/(J(f) + f)
intrinsic TjurinaAlgebraAdapted(f::RngMPolLocElt) -> []
{ An adapted basis for the Tjurina algebra }
  R := Parent(f); g := Rank(R); G := SemiGroup(f);
  Nu1, Nu2 := TjurinaGaps(f); Cv := MaxContactElements(f); B := [];
  for alpha in Nu1 cat Nu2 do
    _, b := SemiGroupMembership(alpha, G); B cat:= [b];
  end for; assert(#B eq TjurinaNumber(f));
  S := [&*[Cv[i]^beta[i] : i in [1..#G]] : beta in B];
  return S;
end intrinsic;

// An 'adapted' basis of the Milnor algebra constructed from any basis
// of the Tjurina algebra.
intrinsic MilnorAlgebraAdapted(f::RngMPolLocElt, RJf::[RngMPolLocElt]) -> []
{ Construct a basis of the Milnor algebra from a basis of the Tjurina algebra }
  R := Parent(f); J := JacobianIdeal(f); kappa := JacobianPower(f);
  for i in [2..kappa] do
    Ji := J + ideal<R | f^i>; tau_i := Dimension(R/Ji);
    Ii := [R | f^(i-1) * gi : gi in RJf | not (f^(i-1) * gi) in Ji];
    RJf cat:= Ii[1..(tau_i - #RJf)];
  end for; return RJf;
end intrinsic;
