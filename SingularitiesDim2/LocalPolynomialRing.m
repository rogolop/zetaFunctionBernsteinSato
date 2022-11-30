// SquarefreePart not available for local polynomial rings.
intrinsic SquarefreePart(f::RngMPolLocElt) -> RngMPolLocElt
{ Return the squarefree part of f, which is the largest (normalized)
  divisor g of f which is squarefree. }

  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return P!SquarefreePart(Q!f);
end intrinsic;

// SquarefreeFactorization not available for local polynomial rings.
intrinsic SquarefreeFactorization(f::RngMPolLocElt) -> SeqEnum
{ Factorize into squarefree polynomials the polynomial f. }

  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return [<P!g[1], g[2]> : g in SquarefreeFactorization(Q!f)];
end intrinsic;

// JacobianMatrix not available for local polynomial rings.
intrinsic JacobianMatrix(poly_list::[RngMPolLocElt]) -> GrpMat
{ Returns the matrix with (i,j)'th entry the partial derivative of the i'th
  polynomial in the list with the j'th indeterminate of its parent ring. }

  P := Parent(poly_list[1]); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return ChangeRing(JacobianMatrix([Q | f : f in poly_list]), P);
end intrinsic;

// Jacobian ideal not available for local polynomial rings.
intrinsic JacobianIdeal(p::RngMPolLocElt) -> RngMPolLoc
{ Returns the ideal generated by all first partial derivatives
  of the polynomial. }

  R := Parent(p); n := Rank(R);
  return ideal<R | [Derivative(p, i) : i in [1..n]]>;
end intrinsic;

// Polynomial not available for local polynomial rings.
intrinsic Polynomial(C::SeqEnum[RngElt], M::SeqEnum[RngMPolLocElt]) -> RngMPolLocElt
{ The multivariate polynomial whose coefficients are C and monomials are M
  (so that Polynomial(Coefficients(f), Monomials(f))) equals f. }

  P := Parent(M[1]); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return P!Polynomial(C, ChangeUniverse(M, Q));
end intrinsic;
