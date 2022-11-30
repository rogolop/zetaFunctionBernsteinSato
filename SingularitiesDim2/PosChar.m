import "Filtration.m": ConvertToIdeal;

// Binary modular exponentiation of f^n mod I with memoization.
ModularExpBinary := procedure(f, n, ~I, ~M)
  R := Parent(f); g := R!1; m := 0; i := 1;
  while n gt 0 do
    if n mod 2 ne 0 then
      n_2 := n mod 2; m +:= i * n_2;
      if M[m] eq 1 then
        if M[i * n_2] eq 1 and g ne R!0 then
          M[i * n_2] := NormalForm(f^n_2, I);
        end if;
        f_n2 := M[i * n_2];
        M[m] := NormalForm(g * f_n2, I);
      end if; g := M[m];
    end if;
    n div:= 2; i *:= 2;
    if n gt 0 then
      if M[i] eq 1 and g ne R!0 then
        M[i] := NormalForm(f * f, I);
      end if; f := M[i];
    end if;
  end while;
end procedure;

// Modular exponentiation of f^n mod I in F_p with fallback
// to binary modular exponentiation and memoization.
ModularExpPadic := procedure(f, n, ~I, ~M)
  R := Parent(f); g := R!1; m := 0; i := 1; p := Characteristic(R);
  if M[1] eq 1 then M[1] := NormalForm(f, I); end if; f := M[1];
  while n gt 0 do
    if n mod p ne 0 then
      n_p := n mod p; m +:= i * n_p;
      if M[m] eq 1 then
        if M[i * n_p] eq 1 and g ne R!0 then
          ModularExpBinary(f, n_p, ~I, ~M);
        end if;
        f_np := M[i * n_p];
        M[m] := NormalForm(g * f_np, I);
      end if; g := M[m];
    end if;
    n div:= p; i *:= p;
    if n gt 0 then
      if M[i] eq 1 and g ne R!0 then
        M[i] := NormalForm(f^p, I);
      end if; f := M[i];
    end if;
  end while;
end procedure;

// Binary search for Nu
NuSearch := procedure(f, e, ~Ip, ~M, ~res)
  p := Characteristic(CoefficientRing(Ip));
  bottom := 0; top := p^e; mid := top div 2;
  while top - 1 gt bottom do
    if M[mid] eq 1 then ModularExpPadic(f, mid, ~Ip, ~M); end if;
    if M[mid] ne 0 then bottom := mid; else top := mid; end if;
    mid := (bottom + top) div 2;
  end while; res := mid;
end procedure;

// General purpose functions to compute the Nu(e) value associated to
// an element f in an ideal I.
intrinsic Nu(f::RngMPolElt, I::RngMPol, e::RngIntElt) -> RngIntElt
{ Computes the nu value of f with respect to the ideal I. }
  R := Parent(f); p := Characteristic(CoefficientRing(R));
  q := Characteristic(CoefficientRing(I));
require p gt 0 and q gt 0: "Computations only valid over finite fields";
require p eq q: "Arguments defined over different finite fields";
require NormalForm(f, I) eq 0: "First argument must be contained in I";
require Basis(I)[1] ne 1 and Gcd(Basis(I)) eq 1:
  "Second argument must be an m-primary ideal";

  Ip := ideal<R | [g^(p^e) : g in Basis(I)]>; res := 0;
  M := [R | 1 : i in [1..p^e]]; NuSearch(f, e, ~Ip, ~M, ~res); return res;
end intrinsic;

// Helper function for ethRoot where the actual computation happens.
ethRootImpl := function(I, e)
  R := Parent(Basis(I)[1]); k := CoefficientRing(R); p := Characteristic(k);

  if e le 0 then return ideal<R | [f^(p^-e) : f in Basis(I)]>; end if;
  n := Rank(R); S := PolynomialRing(k, 2*n, "elim", [1..n], [n+1..2*n]);
  F := hom<R -> S | [S.i : i in [1..n]]>;
  J := ideal<S | [S.(i+n) - (S.i)^(p^e) : i in [1..n]]>;

  // The bulk of the computation.
  G := [NormalForm(F(f), J) : f in Basis(I)];

  // Extract the the 'polynomial' coefficients.
  Q := PolynomialRing(R, n);
  FF := hom<S -> Q | [Q.i : i in [1..n]] cat [R.i : i in [1..n]]>;
  H := &+[ideal<R | Coefficients(FF(g))> : g in G];
  return ideal<R | GroebnerBasis(H)>;
end function;

// Computes the e-th root ideal of an polynomial element using Elimination
intrinsic ethRoot(I::RngMPol, a::RngIntElt, e::RngIntElt) -> RngMPol
{ Computes the ideal (f^a)^[1/p^e]. }
  R := Parent(Basis(I)[1]); k := CoefficientRing(R); p := Characteristic(k);
require p gt 0: "Computations only valid over finite fields";
require p eq #k: "The field must be a prime field";

  A := a div p^e; B := a mod p^e;
  return I^A * ethRootImpl(I^B, e);
end intrinsic;

// The chain of ideals (f^i)^[1/p^e] for i = 1, 2, ...
intrinsic ethRootChain(I::RngMPol, e::RngIntElt) -> []
{ Computes the chain of ethRoots of the powers of f. }
  R := Parent(Basis(I)[1]); k := CoefficientRing(R); p := Characteristic(k);
require p gt 0: "Computations only valid over finite fields";
require p eq #k: "The field must be a prime field";

  S := [<Basis(ethRoot(I, i, e)), i> : i in [1..p^e]]; C := [S[1]];
  for i in [2..p^e] do
    if S[i][1] ne C[#C][1] then Append(~C, S[i]); end if;
  end for; return C;
end intrinsic;

// The Nu invariants of a irreducible plane curve for each ideal in
// the filtration of complete ideals
intrinsic NuFiltration(f::RngMPolLocElt, p::RngIntElt
  : N := -1, e := 1) -> RngIntElt
{ Computes the Nu invariant of f in F_p for each ideal in the filtration
  up to order n. }
  if not IsPrime(p) then error "p must be prime"; end if;
  R<x, y> := LocalPolynomialRing(FiniteField(p), 2);
  F := Filtration(f : N := N); f := R!f;
  M := [R | 1 : i in [1..p^e]]; Nu := [-1 : i in [1..#F]];

  for i in Reverse([1..#F]) do
    MiP := ideal<R | StandardBasis([(R!g)^(p^e) : g in F[i][1]])>;
    M := [R | NormalForm(fi, MiP) : fi in M];
    NuSearch(f, e, ~MiP, ~M, ~Nu[i]);
  end for; return Nu;
end intrinsic;

// The Nu invariants of a irreducible plane curve for each ideal in
// the i-th rupture filtration
intrinsic NuFiltrationRupture(f::RngMPolLocElt, i::RngIntElt, p::RngIntElt
  : N := -1, e := 1) -> RngIntElt
{ Computes the Nu invariant of f in F_p for each ideal in the filtration
  of the i-th rupture divisor. }
  if not IsPrime(p) then error "p must be prime"; end if;
  R<x, y> := LocalPolynomialRing(FiniteField(p), 2);
  F := FiltrationRupture(f, i : N := N); f := R!f;
  M := [R | 1 : i in [1..p^e]]; Nu := [-1 : i in [1..#F]];

  for i in Reverse([1..#F]) do
    MiP := ideal<R | StandardBasis([(R!g)^(p^e) : g in F[i][1]])>;
    M := [R | NormalForm(fi, MiP) : fi in M];
    NuSearch(f, e, ~MiP, ~M, ~Nu[i]);
  end for; return Nu;
end intrinsic;
