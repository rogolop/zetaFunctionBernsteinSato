import "ProximityMatrix.m": ProximityMatrixImpl,
                            ProximityMatrixBranch,
                            MultiplicityVectorBranch,
                            CoefficientsVectorBranch;
import "IntegralClosure.m": IntegralClosureIrreducible,
                            Unloading, ProductIdeals,
                            ClusterFactorization, MaxContactElements;
import "LogResolution.m": ExpandWeightedCluster;
import "SemiGroup.m": TailExponentSeries;

// Helper funcition
ConvertToIdeal := func<I, Q | [&*[g[1]^g[2] : g in f] : f in I]>;

FiltrationRuptureImpl := function(P, e, c, i, niBi)
  // Compute a set of max. cont. elem. of the curve.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex"); ZZ := Integers();
  Pt := Transpose(P); Pt_inv := Pt^-1; N := Pt*P;
  Cv := MaxContactElements(P, e*Pt_inv, c, Q); n := Ncols(P);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, n); max[1][1] := 1; max := max*Pt_inv;

  // Compute the position of the i-th rupture divisor.
  VS := RSpace(ZZ, n); isSat := &+[VS | Pt[i] : i in [1..n]]; R := [];
  for p in [2..n] do // Construct the set of rupture points.
    // Points proximate to 'p' that are free.
    prox_p_free := [i : i in [p + 1..n] | Pt[p][i] eq -1 and isSat[i] ne -1];
    if (isSat[p] eq -1 and (#prox_p_free ge 1 or p eq n)) or
       (isSat[p] ne -1 and #prox_p_free ge 2) then R cat:= [p]; end if;
  end for; Ri := R[i];

  // Construct the i-th cluster.
  vi := ZeroMatrix(IntegerRing(), 1, n); H := [];
  while vi[1][Ri] lt niBi do
    // Unload K_i to get a strictly consistent cluster.
    vi[1][Ri] +:= 1; vi := Unloading(N, vi);

    // Compute generators for the complete ideal H_i.
    Hi := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, vi)];
    Hi := [g[1] : g in ProductIdeals(Hi) |
      &or[g[2][1][i] lt (vi + max)[1][i] : i in [1..n]]];
    H cat:= [<Hi, vi[1][Ri]>];
  end while; return H;
end function;

intrinsic FiltrationRupture(f::RngMPolLocElt, i::RngIntElt : N := -1, Ideal := true) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve associated to the i-th rupture divisor }
require i gt 0: "Second argument must be a positive integer";

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true); ZZ := Integers();
  if #S gt 1 or S[1][2] gt 1 then error "The curve must be irreducible"; end if;
  s := S[1][1]; P, e, c := ProximityMatrixImpl([<s, 1>]); G := SemiGroup(P);
  if i gt #G - 1 then error "Rupture divisor index too large"; end if;
  Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  n := G[1]; Ni := [0] cat [ZZ!(Ei[i] div Ei[i + 1]) : i in [1..#G - 1]];
  if N lt 0 then N := Ni[i + 1] * G[i + 1]; end if;

  F := FiltrationRuptureImpl(P, e[1], c[1], i, N);
  if Ideal eq true then return [<ConvertToIdeal(I[1], Q), I[2]> : I in F];
  else return F; end if;
end intrinsic;

FiltrationImpl := function(s, f, e, M)
  // Compute an upper bound for the necessary points.
  KK := (e*Transpose(e))[1][1]; n := Max(Ncols(e) + M - KK, Ncols(e));
  // Get the proximity matrix with all the necessary points.
  s := PuiseuxExpansionExpandReduced(s, f: Terms := M - KK - 1)[1];
  P := ProximityMatrixBranch(s, n); Pt := Transpose(P); Pt_inv := Pt^-1;
  e := MultiplicityVectorBranch(s, n); c := CoefficientsVectorBranch(s, n);
  N := Pt* P; // Intersection matrix.

  // Compute a set of max. cont. elem. of the curve.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := MaxContactElements(P, e*Pt_inv, c, Q);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, n); max[1][1] := 1; max := max*Pt_inv;

  // Construct the i-th cluster.
  ei := ZeroMatrix(IntegerRing(), 1, n); m_i := 0; H := [];
  while m_i lt M do
    // Get the last points with multiplicity zero.
    I := [i : i in [1..n] | ei[1][i] eq 0][1];
    ei[1][I] := 1; vi := ei*Pt_inv;
    // Unload K_i to get a strictly consistent cluster.
    vi := Unloading(N, vi); ei := vi*Pt;

    // Compute generators for the complete ideal H_i.
    Hi := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, vi)];
    Hi := [g[1] : g in ProductIdeals(Hi) |
      &or[g[2][1][i] lt (vi + max)[1][i] : i in [1..n]]];

    // Fill the gaps in the filtration.
    KK_i := &+[e[i] * ei[1][i] : i in [1..n]]; // Intersection [K, K_i]
    H cat:= [<Hi, KK_i>]; m_i := KK_i;
  end while; return H;
end function;

intrinsic Filtration(f::RngMPolLocElt : N := -1, Ideal := true) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve up to autointersection n }

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  s := S[1][1]; f := S[1][3]; _, e, _ := ProximityMatrixImpl([<s, 1>]);
  KK := e[1]*Transpose(e[1]); // Curve auto-intersection.

  F := FiltrationImpl(s, f, e[1], N lt 0 select KK[1][1] else N);
  if Ideal eq true then return [<ConvertToIdeal(I[1], Q), I[2]> : I in F];
  else return F; end if;
end intrinsic;

TjurinaFiltrationImpl := function(S, f)
  // Get the proximity matrix with all the necessary points.
  P, E, C := ProximityMatrixImpl(S); n := Ncols(P);
  Pt := Transpose(P); Pt_inv := Pt^-1; R := Parent(f); N := Pt*P;
  // The Tjurina ideal & its standard basis.
  J := JacobianIdeal(f) + ideal<R | f>; J := ideal<R | StandardBasis(J)>;

  // Compute a set of max. cont. elem. of the curve.
  A := Parent(C[1][1][2]); Q := LocalPolynomialRing(A, 2, "lglex");
  vi := E[1]*Pt_inv; Cv := MaxContactElements(P, vi, C[1], Q); ZZ := IntegerRing();
  // Add the curve itself as a max. contact element.
  Cvf := <[<Q!f, 1>], vi, E[1]>; Cv cat:= [Cvf];
  // Compute the maximal ideal values.
  max := ZeroMatrix(ZZ, 1, n); max[1][1] := 1; max := max*Pt_inv;

  // Construct the i-th cluster.
  ei := ZeroMatrix(ZZ, 1, n); JJ := []; Hi := ideal<R | 1>; Ji := Hi meet J;
  while Hi ne Ji do
    // Enlarge, if necessary, the cluster with one point on the curve.
    I := [i : i in [1..n] | ei[1][i] eq 0];
    if #I eq 0 then
      ExpandWeightedCluster(~P, ~E, ~C, ~S, -1); n := n + 1; P[n][n - 1] := -1;
      E[1][1][n] := 1; ei := E[1]; Pt := Transpose(P); Pt_inv := Pt^-1;
      // Expand (i.e. blow-up an extra point) the maximal ideal.
      max := ZeroMatrix(ZZ, 1, n); max[1][1] := 1; max := max*Pt_inv;

      newCv := []; // Expand (i.e. blow-up an extra points) the max. cont. elem.
      for i in [1..#Cv] do
        Ei := InsertBlock(ZeroMatrix(ZZ, 1, n), Cv[i][3], 1, 1);
        if i eq #Cv then Ei[1][n] := 1; end if; // The last max. cont. elem. is f.
        newCv cat:= [<Cv[i][1], Ei*Pt_inv, Ei>];
      end for; Cv := newCv;
    else ei[1][I[1]] := 1; end if;

    // Unload K_i to get a strictly consistent cluster.
    vi := ei*Pt^-1; vi := Unloading(N, vi); ei := vi*Pt;

    // Compute generators for the complete ideal H_i.
    Hi := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q)
      : v_j in ClusterFactorization(P, vi)];
    Hi := [g[1] : g in ProductIdeals(Hi) | &or[g[2][1][i] lt
      (vi + max)[1][i] : i in [1..n]]];
    Hi := ideal<R | ConvertToIdeal(Hi, R)>; Ji := Hi meet J;
    // Ignore the begining of the filtration.
    if Ji eq J then continue;
    else JJ cat:= [<Ji, vi[1][Ncols(vi)]>];
    end if;
  end while; return JJ;
end function;

intrinsic TjurinaFiltration(f::RngMPolLocElt) -> []
{ Returns an adapted filtration of the Tjurina ideal of an irreducible
  plane curve }

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  return TjurinaFiltrationImpl(S, f);
end intrinsic;
