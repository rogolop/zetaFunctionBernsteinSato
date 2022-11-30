import "ProximityMatrix.m": ProximityMatrixImpl, CoefficientsVectorBranch;

ExpandWeightedCluster := procedure(~P, ~EE, ~CC, ~S, b)
  // Expand the proximity matrix.
  P := InsertBlock(ScalarMatrix(Ncols(P) + 1, 1), P, 1, 1); N := Ncols(P);
  // Expand branches multiplicities.
  EE := [InsertBlock(ZeroMatrix(IntegerRing(), 1, N), EEi, 1, 1)
     : EEi in EE];
  // If a free points, it has mult. 1 in the branch & expand the Puiseux series.
  if b ne -1 then
    EE[b][1, N] := 1;
    // Number of points of branch b appearing in BP(I)
    m := #[e : e in Eltseq(EE[b]) | e ne 0];
    // If we do not have enough terms of Puiseux already computed...
    if #CC[b] lt m + 1 then
      SS := PuiseuxExpansionExpandReduced(S[b][1], S[b][3]:
        Terms := m + 1 - #CC[b], Polynomial := true)[1];
      S[b][1] := SS[1]; S[b][3] := SS[2];
      CC[b] := CoefficientsVectorBranch(S[b][1], m + 1);
    end if;
  end if;
end procedure;

ComputeLogResolutionData := procedure(~P, ~EE, ~CC, ~S, N, ~E, ~C, ~V, ~v)
  // Compute the multiplicities of each generator in G.
  E := [ZeroMatrix(IntegerRing(), 1, Ncols(P)) : i in [1..N]];
  // Hold information about the branches in each generator.
  for i in [1..#S] do for m in S[i][2] do
    E[m[2]] := E[m[2]] + m[1] * EE[i];
  end for; end for;
  // Merge the coefficients of each branch.
  C := [#CC gt 0 select Parent(CC[1][2]) else RationalField()
    | <0, 1> : i in [1..Ncols(P)]];
  for i in [1..#EE] do
    I := [j : j in [1..Ncols(P)] | EE[i][1][j] ne 0];
    for j in [1..#I] do C[I[j]] := CC[i][j]; end for;
  end for;
  // Values for each generator in G & each (initial) base point.
  Pt_inv := Transpose(P^-1); V := [e * Pt_inv : e in E];
  v := ZeroMatrix(IntegerRing(), 1, Ncols(P));
  for i in [1..Ncols(P)] do v[1][i] := Min([vj[1][i] : vj in V]); end for;
end procedure;

intrinsic LogResolution(I::RngMPolLoc : Coefficients := false) -> []
{ Computes the weighted cluster of base points of a bivariate
  polynomial ideal I }
  // Generators in G & fixed part F.
  G := Basis(I); F := Gcd(G); G := [ExactQuotient(g, F) : g in G];

  ////////////// Compute all information ////////////////
  S := PuiseuxExpansion(G: Polynomial := true);
  P, EE, CC := ProximityMatrixImpl([*<s[1], 1> : s in S*]: ExtraPoint := true);

  E := []; // Multiplicities of each generator.
  C := []; // Coefficients of BP(I).
  V := []; // Vector a values for each generator.
  v := []; // Virtual values of BP(I).
  ComputeLogResolutionData(~P, ~EE, ~CC, ~S, #G, ~E, ~C, ~V, ~v);

  /////////////// Add new free points /////////////////////
  lastFree := [i : i in [1..Ncols(P)] | (&+P[1..Ncols(P)])[i] eq 1];
  points2test := #lastFree; idx := 1;
  // For each last free point on a branch...
  while points2test gt 0 do
    // Values for each gen. at p.
    p := lastFree[idx]; Vp := [vi[1][p] : vi in V];
    // Generators achieving the minimum.
    GG := [i : i in [1..#Vp] | Vp[i] eq Min(Vp)];
    // If the multiplicities of all the generators achieving the minimum
    // at p is > 0 add new point.
    if &and[E[g][1][p] ne 0 : g in GG] then
      // The (unique) branch of the generator 'g' where 'p' belongs.
      assert(#[i : i in [1..#EE] | EE[i][1, p] ne 0] eq 1);
      b := [i : i in [1..#EE] | EE[i][1, p] ne 0][1];
      ExpandWeightedCluster(~P, ~EE, ~CC, ~S, b); P[Ncols(P)][p] := -1;
      ComputeLogResolutionData(~P, ~EE, ~CC, ~S, #G, ~E, ~C, ~V, ~v);
      // We may need to add more free points after the points we added.
      lastFree cat:= [Ncols(P)]; points2test := points2test + 1;
    end if;
  points2test := points2test - 1; idx := idx + 1;
  end while;

  /////////////// Add new satellite points /////////////////////
  points2test := Ncols(P) - 1; p := 2; // Do not start at the origin.
  while points2test gt 0 do
    // Values for the generators at point p.
    Vp := [vi[1][p] - v[1][p] : vi in V];
    // Points p is proximate to && Points proximate to p.
    p_prox := [i : i in [1..Ncols(P)] | P[p][i] eq -1];
    prox_p := [i : i in [1..Ncols(P)] | P[i][p] eq -1];
    Q := [q : q in p_prox | &+Eltseq(Submatrix(P, prox_p, [q])) eq 0];
    for q in Q do
      // Values for the generators at point q.
      Vq := [vi[1][q] - v[1][q] : vi in V];
      if &*[Vp[i] + Vq[i] : i in [1..#Vp]] ne 0 then
        ExpandWeightedCluster(~P, ~EE, ~CC, ~S, -1);
        P[Ncols(P)][p] := -1; P[Ncols(P)][q] := -1;
        ComputeLogResolutionData(~P, ~EE, ~CC, ~S, #G, ~E, ~C, ~V, ~v);
        // We may need to add more satellite points after the points we added.
        points2test := points2test + 1;
      end if;
    end for;
  points2test := points2test - 1; p := p + 1;
  end while;

  /////////////// Remove non base points ////////////////
  // Multiplicities for the cluster of base points.
  e := v * Transpose(P); I := [i : i in [1..Ncols(P)] | e[1][i] ne 0];
  // Remove points not in the cluster of base points.
  P := Submatrix(P, I, I); v := Submatrix(v, [1], I); C := C[I];

  // Select 1 as affine part iff F is a unit.
  F := Evaluate(F, <0, 0>) ne 0 select Parent(F)!1 else F;
  if Coefficients then return P, v, F, C;
  else return P, v, F; end if;
end intrinsic;
