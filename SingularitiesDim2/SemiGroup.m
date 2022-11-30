Euclides := function(m, n)
  hs := []; ns := [];
  while n ne 0 do
    Append(~hs, m div n); Append(~ns, n);
    r := m mod n; m := n; n := r;
  end while; return <hs, ns>;
end function;

intrinsic CharExponents(s::RngSerPuisElt) -> []
{ Returns the characteristic exponents of a Puiseux series }
  C, m, n := ElementToSequence(s);
  // Exponents appearing in the series s
  E := [m + i - 1 : i in [1 .. #C] | C[i] ne 0];
  charExps := [<0, n>]; ni := n;
  while ni ne 1 do
    // m_i = min{ j | a_j != 0 and j \not\in (n_{i-1}) }
    mi := [e : e in E | e mod ni ne 0][1];
    // n_i = gcd(n, m_1, ..., m_k)
    ni := Gcd(ni, mi); Append(~charExps, <mi, ni>);
  end while; return charExps;
end intrinsic;

intrinsic CharExponents(f::RngMPolLocElt) -> []
{ Returns the characteristic exponents of an irreducible bivariate polynomials }
  S := PuiseuxExpansion(f);
  if #S ne 1 then error "Argument must be a irreducible series"; end if;
  if S[1][2] ne 1 then error "Argument must be a reduced series"; end if;
  return CharExponents(S[1][1]);
end intrinsic;

intrinsic CharExponents(G::[RngIntElt] : Plane := true) -> []
{ Computes the characteristic exponents from the generators of the semigroup }
if Plane eq true then
  require IsPlaneCurveSemiGroup(G): "G is not the semigroup of a plane curve";
end if;

  M := [G[1]]; N := [G[1]];
  for i in [2..#G] do
    M cat:= [ &+[j ne i select -(N[j - 1] - N[j]) div N[i - 1] * M[j]
      else G[j] : j in [2..i]] ]; N cat:= [Gcd(M)];
  end for;
  return [<0, N[1]>] cat [<M[i], N[i]> : i in [2..#M]];
end intrinsic;

TailExponentSeries := function(s)
  C, m, n := ElementToSequence(s);
  // Exponents appearing in the series s
  E := [m + i - 1 : i in [1..#C] | C[i] ne 0];
  charExps := CharExponents(s); g := #charExps;
  if s eq 0 then return <0, 1>; end if;
  return [<e, 1> : e in Reverse(E) | e ge charExps[g][1]][1];
end function;

TailExponentMatrix := function(P)
  E := CharExponents(SemiGroup(P)); N := Ncols(P);
  // If last point is satellite there is no tail exponent
  if &+Eltseq(P[N]) eq -1 then error "no free point"; end if;
  Pt := Transpose(P); isSat := &+[Pt[j]: j in [1..N]];
  p := ([i : i in Reverse([1..N]) | isSat[i] eq -1] cat [0])[1] + 1;
  return <E[#E][1] + (N - p), 1>;
end function;

intrinsic SemiGroup(n::RngIntElt, M::[RngIntElt]) -> []
{ Computes a minimal set of generators for the semigroup associated
  to a set of charactetistic exponents }
require IsCharSequence(n, M) : "Argument must be a valid char. sequence";

  E := [i gt 1 select Gcd(Self(i - 1), M[i - 1]) else n : i in [1..#M + 1]];
  G := [i gt 2 select ( (Self(i - 1) - M[i - 2]) * E[i - 2] div E[i - 1] ) +
    M[i - 1] + ( (E[i - 2] - E[i - 1]) div E[i - 1] ) * M[i - 2]
        else [n, M[1]][i] : i in [1..#M + 1]];
  return Sort(G);
end intrinsic;

intrinsic SemiGroup(s::RngSerPuisElt) -> []
{ Computes a minimal set of generators for the semigroup of the
  Puiseux series of an irreducible plane curve }

  M := CharExponents(s); // (G)amma starts with <n, m, ...>
  return SemiGroup(M[1][2], [M[i][1] : i in [2..#M]]);
end intrinsic;

intrinsic SemiGroup(f::RngMPolLocElt) -> []
{ Computes a minimal set of generators for the semigroup of
  and irreducible plane curve }

  S := PuiseuxExpansion(f);
  if #S ne 1 then error "Argument must be an irreducible series"; end if;
  if S[1][2] ne 1 then error "Argument must be a reduced series"; end if;

  return SemiGroup(S[1][1]);
end intrinsic;

intrinsic SemiGroup(P::Mtrx : UseExtraPoints := false) -> []
{ Returns the minimal set of generators for the semigroup of and irreducible
  plane curve from its weighted cluster of singular points }
require Ncols(P) eq Nrows(P):
  "Proximity matrix does not have the required dimensions";
require CoefficientRing(P) eq Integers():
  "Proximity matrix must be defined over the integers";
require IsInvertible(P):
  "Proximity matrix must be invertible";
require IsUnipotent(P):
  "Proximity matrix must be unipotent";

  if Ncols(P) eq 0 then return [1, 0]; end if;
  N := Ncols(P); e := ZeroMatrix(Integers(), 1, N); e[1, N] := 1; e := e*P^-1;
  Pt := Transpose(P); v := e*Pt^-1; isSat := &+[Pt[i] : i in [1..N]];
  G := [v[1][1]]; G cat:= [v[1][i] : i in [1..N - 1] |
    isSat[i] ne -1 and isSat[i + 1] eq -1];
  if UseExtraPoints and &+Eltseq(P[N]) ne -1 then return G cat [v[1, N]];
  else return G; end if;
end intrinsic;

forward SemiGroupMemberImpl;

SemiGroupMemberImpl := procedure(v, i, ~G, ~B, ~b, ~V)
  if v lt 0 or i gt #G then b := 0; return; end if;
  if B[v + 1, i] ne -1 then b := B[v + 1, i]; return; end if;
  V[i] := V[i] + 1;
  SemiGroupMemberImpl(v - G[i], i, ~G, ~B, ~b, ~V);
  B[v + 1, i] := b; if b eq 1 then return; end if;
  V[i] := V[i] - 1;
  SemiGroupMemberImpl(v, i + 1, ~G, ~B, ~b, ~V);
  B[v + 1, i] := b; if b eq 1 then return; end if;
end procedure;

intrinsic SemiGroupMembership(v::RngIntElt, G::[RngIntElt]) -> BoolElt
{ Returns whether or not an integer v belongs to a numerical semigroup G and
  the coordinates v in the semigroup }

  V := [0 : i in [1..#G]];
  if v lt 0 then return false, V; end if;
  // Any semigroup is valid.
  B := Matrix(v + 1, #G, [IntegerRing() | -1 : i in [1..(v + 1) * #G]]);
  for i in [1..#G] do B[0 + 1][i] := 1; end for;
  b := 0; SemiGroupMemberImpl(v, 1, ~G, ~B, ~b, ~V);
  return b eq 1, V;
end intrinsic;

InversionFormula := function(M0, P, c)
  // Compute the exp. of the last free pt. depending of the first char. exp.
  N := Ncols(P); Pt := Transpose(P); isSat := &+[Pt[j]: j in [1..N]];
  p := ([i : i in [1..N] | isSat[i] eq -1] cat [N + 1])[1] - 1;
  m := ([i : i in [2..p] | c[i][1] ne 0] cat [0])[1] - 1;
  // Depending on whether 'm' is 0 or not, we have case (a) or case (b).
  M1 := [<0, m eq -1 select M0[2][1] else Lcm(M0[1][2], m)>]; k := #M0 - 1;
  M1 cat:= [<M0[1][2], Gcd(M1[1][2], M0[1][2])>]; i0 := m eq -1 select 2 else 1;
  ni := M1[2][2]; // ni := gcd(n, m_1, ..., m_i)
  for i in [i0..k] do // \bar{mi} = mi + n - \bar{n}
    mi := M0[i + 1][1] + M0[1][2] - M1[1][2];
    ni := Gcd(ni, mi); M1 cat:= [<mi, ni>];
  end for; return M1;
end function;

intrinsic IsPlaneCurveSemiGroup(G::[RngIntElt]) -> BoolElt
{ Whether the semigroup is a plane curve semigroup or not }

  if Gcd(G) ne 1 then return false; end if;
  // e_i := gcd(\bar{m}_{i-1}, \bar{m}_i)
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  // n_i := e_i / e_{i + 1}
  N := [1] cat [E[i] div E[i + 1] : i in [1..#G - 1]];
  // n_i != 1 for all i (iff e_i > e_{i+1})
  if Position(N[2..#N], 1) ne 0 then return false; end if;
  // n_i \bar{m}_{i} \in < m_{0}, ..., m_{i-1} > &&
  // n_i \bar{m}_i < \bar{m}_{i + 1} &&
  if not &and[SemiGroupMembership(N[i] * G[i], G[[1..i - 1]]) : i in [2..#G]] or
     not &and[N[i] * G[i] lt G[i + 1] : i in [1..#G - 1]] then return false;
  end if; return true;
end intrinsic;

intrinsic IsCharSequence(n::RngIntElt, M::[RngIntElt]) -> BoolElt
{ Whether the inputs is a valid characteristic sequence or not }
  // e_i := gcd(e_{i-1}, m_i)
  E := [i gt 1 select Gcd(Self(i - 1), M[i - 1]) else n : i in [1..#M + 1]];
  if Sort(E) eq Reverse(E) and E[#E] eq 1 and E[#E - 1] ne 1 then
  return true; else return false; end if;
end intrinsic;

intrinsic Conductor(G::[RngIntElt]) -> RngIntElt
{ Returns the conductor of the semigroup G }
require IsPlaneCurveSemiGroup(G): "Argument must be a plane curve semigroup";

  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]]; g := #G - 1; n := G[1];
  return &+[(N[i] - 1) * G[i + 1] : i in [1..g]] - n + 1;
end intrinsic;

intrinsic Conductor(n::RngIntElt, M::[RngIntElt]) -> RngIntElt
{ Returns the conductor of the char. exponents (n, M) }

  return Conductor(SemiGroup(n, M));
end intrinsic;

intrinsic Conductor(s::RngSerPuisElt) -> RngIntElt
{ Returns the conductor of the Puiseux series s }

  return Conductor(SemiGroup(s));
end intrinsic;

intrinsic Conductor(f::RngMPolLocElt) -> RngIntElt
{ Returns the conductor of the irreducible plane curve f }

  return Conductor(SemiGroup(f));
end intrinsic;

forward SemiGroupCoordImpl;

SemiGroupCoordImpl := function(v, i, G);
  if v eq 0 then return [[0 : i in [1..#G]]]; end if;
  if v lt 0 or i gt #G then return []; end if; CC := [];

  for k in Reverse([0..(v div G[i])]) do
    T := SemiGroupCoordImpl(v - k * G[i], i + 1, G);
    for j in [1..#T] do T[j][i] := k; CC cat:= [T[j]]; end for;
  end for; return CC;
end function;

intrinsic SemiGroupCoord(v::RngIntElt, G::[RngIntElt]) -> []
{ Return the coordinates of an integer v in the numerical semigroup G }

  return SemiGroupCoordImpl(v, 1, G);
end intrinsic;

intrinsic SemiGroup(L::[SeqEnum]) -> []
{ Constructs a semigroup from the semigroup of each characteristic exponent }
require #L ne 0: "List must be non-empty";
require &and[#S eq 2 : S in L]: "Input semigroup must have two elements";

  P := ProximityMatrix(L[1]); ZZ := Integers();
  for i in [2..#L] do
    Qi := ProximityMatrix(L[i]); N := Ncols(P); Ni := Ncols(Qi);
    P := DiagonalJoin(P, ZeroMatrix(ZZ, Ni - 1, Ni - 1));
    InsertBlock(~P, Qi, N, N);
  end for; return SemiGroup(P);
end intrinsic;
