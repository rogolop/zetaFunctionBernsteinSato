/*
  Author: Roger Gomez Lopez
  
  Modified functions for working with all possibilities (instead of choosing one automatically)
  for the semigroup coordinates, monomial curves, and deformations
*/


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


intrinsic DeformationCurveSpecific(monomialCurve::SeqEnum[RngMPolElt], G::SeqEnum[RngIntElt]) -> SeqEnum[RngMPolLocElt]
  {
    Computes the deformation of the monomial curve associated to the semigroup "G" with the specific choice of equations "monomialCurve".
    Implementation based on "DeformationCurve(G::[RngIntElt])" from "SingularitiesDim2/Misc.m"
  }

  I := monomialCurve; // Choose this particular monomial curve equations
  
  // The rest is copied code:
  
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
