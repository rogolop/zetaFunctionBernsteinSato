xFactor := function(f)
  return Min([IntegerRing() | Exponents(t)[1] : t in Terms(f)]);
end function;

yFactor := function(f)
  return Min([IntegerRing() | Exponents(t)[2] : t in Terms(f)]);
end function;

forward PuiseuxExpansionLoop;

intrinsic PuiseuxExpansion(f::RngMPolLocElt : Terms := -1,
                                              Polynomial := false) -> [ ]
{ Computes the Puiseux expansion of any bivariate polynomial }
require Rank(Parent(f)) eq 2: "Argument must be a bivariate polynomial";
  // If Nf start on the right of the x-axis, we have an x-factor.
  yBranch := (xFactor(f) gt 0) select [* <Parent(f).1,
    [<xFactor(f), 1>], Parent(f).1> *] else [* *];

  P<x, y> := LocalPolynomialRing(AlgebraicClosure(
    CoefficientRing(Parent(f))), 2, "lglex");
  S := yBranch cat SequenceToList(PuiseuxExpansionLoop(P!SquarefreePart(f),
    [<P!g[1], g[2], 1> : g in SquarefreeFactorization(f)], Terms - 1));
  if not Polynomial then return [* <s[1], s[2][1][1]> : s in S *];
  else return [* <s[1], s[2][1][1], s[3]> : s in S *]; end if;
end intrinsic;

intrinsic PuiseuxExpansion(L::[RngMPolLocElt] : Terms := -1,
                                                Polynomial := false) -> [ ]
{ Computes the Puiseux expansion for the product of all the elements of L }
require #L gt 0: "Argument must be a non-empty list";
require &and[Rank(Parent(f)) eq 2 : f in L]:
  "Elements of L must be bivariate polynomials";

  f := &*L;
  P<x, y> := LocalPolynomialRing(AlgebraicClosure(
    CoefficientRing(Parent(f))), 2, "lglex");
  // If Nf start on the right of the x-axis, we have an x-factor.
  yBranch := (xFactor(f) gt 0) select [* <Parent(f).1,
    [<xFactor(L[i]), i> : i in [1..#L] | xFactor(L[i]) ne 0], x> *] else [* *];

  sqFreePart := P!SquarefreePart(f); sqFreeFact := [];
  for i in [1..#L] do
    sqFreeFact cat:= [<P!g[1], g[2], i>: g in SquarefreeFactorization(L[i])
      | Evaluate(L[i], <0, 0>) eq 0];
  end for;
  S := yBranch cat SequenceToList(PuiseuxExpansionLoop(sqFreePart,
    sqFreeFact, Terms - 1));

  // Return the polynomial residue if requested.
  if not Polynomial then return [* <s[1], s[2]> : s in S *];
  else return S; end if;
end intrinsic;

PuiseuxExpansionLoop := function(f, L, terms)
  Q<t> := PuiseuxSeriesRing(CoefficientRing(Parent(f)));
  x := Parent(f).1; y := Parent(f).2;
  // Step (i.a): Select only those factors containing the 0 branch.
  S := yFactor(f) gt 0 select [<Q!0, [<g[2], g[3]> : g in L
    | yFactor(g[1]) ne 0], y>] else [];
  // Step (i.b): For each side...
  for F in NewtonSides(f, NewtonPolygon(f)) do
    n := F[1]; m := F[2]; P := F[3];
    // Apply the change of variables (1).
    C := Reverse(Coefficients(n eq 1 select f else Evaluate(f, 1, x^n), 2));
    CL := [<Reverse(Coefficients(n eq 1 select g[1] else
      Evaluate(g[1], 1, x^n), 2)), g[2], g[3]> : g in L];
    // For each root...
    for a in [<Root(a[1], n), a[2]> : a in Roots(P)] do
      // Apply the change of variables (2) & get the sub-solution recursively.
      ff := [i gt 1 select C[i] + Self(i - 1) * x^m * (a[1] + y) else C[1]
         : i in [1..#C]][#C];
      LL := [<[i gt 1 select Cj[1][i] + Self(i - 1) * x^m * (a[1] + y) else
        Cj[1][1] : i in [1..#Cj[1]]][#Cj[1]], Cj[2], Cj[3]> : Cj in CL];
      // Select only those factors that contain the current branch.
      LL := [g : g in LL | NewtonPolygon(g[1])[1][2] ne 0];
      // If the mult. of a is greater than 1 continue.
      R := (a[2] ne 1 and terms lt -1) or terms gt 0 select
        PuiseuxExpansionLoop(ff, LL, terms - 1) else
          [<Q!0, [<g[2], g[3]> : g in LL], ff>];
      // Undo the change of variables.
      S cat:= [<t^(m/n) * (a[1] + Composition(s[1], t^(1/n))), s[2], s[3]>
           : s in R];
    end for;
  end for; return S;
end function;

forward PuiseuxExpansionReducedLoop;

intrinsic PuiseuxExpansionReduced(f::RngMPolLocElt : Terms := -1,
                                                     Polynomial := false) -> [ ]
{ Computes the Puiseux expansion of a reduced bivariate polynomial }
require Rank(Parent(f)) eq 2: "Argument must be a bivariate polynomial";

  P := LocalPolynomialRing(AlgebraicClosure(
    CoefficientRing(Parent(f))), 2, "lglex");
  // If Nf start on the right of the x-axis, we have an x-factor.
  yBranch := (xFactor(f) gt 0) select [<Parent(f).1, P.1>] else [];

  S := yBranch cat PuiseuxExpansionReducedLoop(
    P!SquarefreePart(f), Terms - 1);
  if Polynomial then return S; else return [s[1] : s in S]; end if;
end intrinsic;

intrinsic PuiseuxExpansionExpandReduced(s::RngSerPuisElt, f::RngMPolLocElt
                                      : Terms := 1, Polynomial := false) -> [ ]
{ Expands the Puiseux expansion s of a reduced bivariate polynomial }
require Rank(Parent(f)) eq 2: "Argument f must be a bivariate polynomial";

  n := ExponentDenominator(s); x := Parent(s).1;
  m := s eq 0 select 0 else Degree(s);

  S := Terms gt 0 select PuiseuxExpansionReducedLoop(f, Terms - 1)
       else [<PuiseuxSeriesRing(CoefficientRing(Parent(f)))!0, f>];
  P<t> := PuiseuxSeriesRing(CoefficientRing(Parent(s)));
  if Polynomial then return [<s + t^m * Composition(si[1], t^(1/n)), si[2]>
    : si in S];
  else return [s + t^m * Composition(si[1], t^(1/n)): si in S]; end if;
end intrinsic;

intrinsic PuiseuxExpansionExpandReduced(x::RngMPolLocElt, f::RngMPolLocElt
                                      : Terms := 1, Polynomial := false) -> [ ]
{ Expands the Puiseux expansion s of a reduced bivariate polynomial }
require Rank(Parent(f)) eq 2: "Argument f must be a bivariate polynomial";

  if Polynomial then return [<x, x>]; else return [x]; end if;
end intrinsic;

PuiseuxExpansionReducedLoop := function(f, terms)
  Q<t> := PuiseuxSeriesRing(CoefficientRing(Parent(f)));
  x := Parent(f).1; y := Parent(f).2;
  // Step (i.a): Select only those factors containing the 0 branch.
  S := yFactor(f) gt 0 select [<Q!0, y>] else [];
  // Step (i.b): For each side...
  for F in NewtonSides(f, NewtonPolygon(f)) do
    n := F[1]; m := F[2]; P := F[3];
    // Apply the change of variables (1).
    C := Reverse(Coefficients(n eq 1 select f else Evaluate(f, 1, x^n), 2));
    // For each root...
    for a in [<Root(a[1], n), a[2]> : a in Roots(P)] do
      // Apply the change of variables (2) & get the sub-solution recursively.
      g := [i gt 1 select C[i] + Self(i - 1) * x^m * (a[1] + y) else C[1]
         : i in [1..#C]][#C];
      R := (a[2] ne 1 and terms lt -1) or terms gt 0 select
        PuiseuxExpansionReducedLoop(g, terms - 1) else [<Q!0, g>];
      // Undo the change of variables.
      S cat:= [<t^(m/n) * (a[1] + Composition(s[1], t^(1/n))), s[2]> : s in R];
    end for;
  end for; return S;
end function;
