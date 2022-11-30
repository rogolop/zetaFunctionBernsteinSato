/*
  Author: Roger Gomez Lopez
  
  Blowups, transforms, information derived from the semigroup
*/


function xFactor(f)
  // minimum (common) x exponent in f (with f != 0)
  return Min([IntegerRing() | Exponents(term)[1] : term in Terms(f)]);
end function;


function yFactor(f)
  // minimum (common) y exponent in f (with f != 0)
  return Min([IntegerRing() | Exponents(term)[2] : term in Terms(f)]);
end function;


function nFactor(f, n)
  // minimum (common) x_n exponent in f (with f != 0)
  return Min([IntegerRing() | Exponents(term)[n] : term in Terms(f)]);
end function;


function MatToSeq(M)
  // Sequence containing all matrix elements (preserving index if size is 1xN or Nx1)
  return [ M[i,j] : i in [1..Nrows(M)], j in [1..Ncols(M)] ];
end function;



// Information related to the curve and its blowup(s)

intrinsic SemiGroupInfo(_betas::[]) -> Tup
  {
    Numbers related to the semigroup and the characteristic exponents.
    Input: _betas -> generators of the semigroup
    Theory indexing of all sequences 0..g -> Magma indexing 1..(g+1)
  }
  g := #_betas - 1; // Number of characteristic exponents (see PHD-Guillem, p.25)
  n := _betas[1]; // Multiplicity of the curve at the origin (see PHD-Guillem, p.24)
  
  charExpsData := CharExponents(_betas); // [<beta_i,e_i>]
  betas := [cExp[1] : cExp in charExpsData]; // defining beta_0=0
  es := [cExp[2] : cExp in charExpsData];
  
  ms := [betas[i] div es[i] : i in [1..g+1]]; // defining m_0=0, m_i=beta_i/e_i (see PHD-Guillem, p.24)
  ns := [0] cat [es[i-1] div es[i] : i in [2..g+1]]; // n_0=0, n_i=e_{i-1}/e_i (see PHD-Guillem, p.24)
  _ms := [_betas[i] div es[i] : i in [1..g+1]]; // _m_i=_beta_i/e_i (see PHD-Guillem, p.25)
  qs := [0] cat [ms[i] - ns[i]*ms[i-1] : i in [2..g+1]]; // q_i=m_i-n_i*m_{i-1} (see PHD-Guillem, p.25)
  c := ns[g+1]*_betas[g+1] - betas[g+1] - (n-1); // Conductor of the semigroup / Milnor number, c=n_g*_beta_g-beta_g-(n-1) (see PHD-Guillem, p.25)

  // Characteristic exponents
  //[betas[i] / n : i in [1..g+1]];
  //[ms[i] / &*(ns[2..i+1]) : i in [1..g+1]];
  //PuiseuxExpansionReduced(f);
  
  return < g, c, betas, es, ms, ns, qs, _ms >;
end intrinsic;


intrinsic MultiplicitiesAtAllRuptureDivisors(f::RngMPolLocElt) -> [], [], [], []
  {
    Multiplicities of the rupture divisors and their adjacent divisors
  }
  // All multiplicities
  ProxMat, e := ProximityMatrix(f : ExtraPoint := true); // e: strict transform multiplicities
  N := e*Transpose(ProxMat^-1); // (see TFG-Roger, p.16, Prop.2.3.21)
  N := MatToSeq(N); // N: total transform multiplicities
  ones := Matrix([[1 : i in [1..Ncols(ProxMat)]]]); // row matrix (1,...,1)
  k := ones*Transpose(ProxMat^-1); // (see TFG-Roger, p.17, Prop.2.3.22)
  k := MatToSeq(k); // k: canonical divisor multiplicities
  e := MatToSeq(e); // e: strict transform multiplicities
  
  // Multiplicities at rupture divisors
  E := -Transpose(ProxMat)*ProxMat; // Dual graph matrix / intersection matrix (see TFG-Roger, p.18, Def.2.3.23)
  EE := RowSequence(E - DiagonalMatrix(Integers(), Diagonal(E))); // Remove diagonal, now EE[i][j]=1 if i!=j and Ei intersects Ej, else EE[i][j]=0
  Rup := [i : i in [1..Ncols(ProxMat)] | &+EE[i] ge 3]; // Rupture divisors' indexes (divisors with >=3 intersections)
  Nps := N[Rup]; // N of rupture divisors
  kps := k[Rup]; // k of rupture divisor
    
  // Multiplicities of divisors adjacent to each rupture divisor
  Ns := [];
  ks := [];
  for p in Rup[1..#Rup] do
    Adj_p := [i : i in [1..Ncols(ProxMat)] | E[p][i] eq 1]; // indexes of divisors adjacent to each rupture divisor (they intersect)
    Append(~Ns, N[Adj_p]); // N's of adjacent divisors
    Append(~ks, k[Adj_p]); // k's of adjacent divisors
    Ns[#Ns,3] := e[p]; //e[Adj_p[3]]; // e of the curve (see TFG-Roger, p.27, Def.4.2.1)
    ks[#ks,3] := 0; // k of the curve (see TFG-Roger, p.27, Def.4.2.1)
  end for;
  
  return Nps, kps, Ns, ks;
end intrinsic;


intrinsic MultiplicitiesAtThisRuptureDivisor(r::RngIntElt, Nps::[], kps::[], Ns::[], ks::[]) -> RngIntElt, RngIntElt, [], []
  {
    Multiplicities of the r-th rupture divisor and its adjacent divisors
  }
  Np := Nps[r]; // N of rupture divisor
  kp := kps[r]; // k of rupture divisor
  N := Ns[r]; // N's of adjacent divisors
  k := ks[r]; // k's of adjacent divisors
  return Np, kp, N, k;
end intrinsic;


intrinsic Nus(_betas, semiGroupInfo, Np, kp, r : discardTopologial:=true) -> [], []
  {
    Values of nu which may correspond to a varying root of the Bernstein-Sato polynomial, and topological roots
  }
  g, c, betas, es, ms, ns, qs, _ms := Explode(semiGroupInfo);
  
  // All possible nus (see TFG-Roger, p.29, Cor.4.2.12)
  nus := [0..(Np-1)];
  
  // Discard nus corresponding to the other divisors crossing the r-th exceptional divisor (they never correspond to roots of the Bernstein-Sato-polynomial, and they may give infinities and zeros at the calculation of the residue of the complex zeta function)
  // Conditions: _beta_r*sigma not integer
  //             e_{r-1}*sigma not integer
  // (see TFG-Roger, p.28, Th.4.2.6)
  Z := IntegerRing();
  nus := [nu : nu in nus | _betas[r+1]*Sigma(Np,kp,nu) notin Z and es[r]*Sigma(Np,kp,nu) notin Z ];
  
  // Topological roots of Bernstein-Sato polynomial (they are always roots of the Bernstein-Sato polynomial, they give unit (=> nonzero) residues of the complex zeta function) (see TFG-Roger, p.28-29)
  // They are the nus corresponding to:
  //   semigroup of the divisorial valuation of Er == semigroup of the (r+1)-th maximal contact element
  // (see PHD-Guillem p.120 Theorem 12.3, p.26 Lemma 2.10, p.26 eq.2.22, beware the inconsistent notation Gamma_i)
  r := r+1;
  G_r := [ &*(ns[[(j+1)..r]]) * _ms[j] : j in [1..r] ];
  while 0 in G_r do Exclude(~G_r, 0); end while; // Remove all 0's in G_r
  topologicalNus := [nu : nu in nus | SemiGroupMembership(nu, G_r)];
  
  if discardTopologial then
    nus := [nu : nu in nus | nu notin topologicalNus];
  end if;
  
  return nus, topologicalNus;
end intrinsic;


intrinsic Sigma(Np::RngIntElt, kp::RngIntElt, nu::RngIntElt) -> FldRatElt
  {
    Root candidate corresponding to a nu
  }
  return - (kp + 1 + nu) / Np; // (see TFG-Roger p.27 eq.4.2.1)
end intrinsic;


// Apply changes of variables

intrinsic StrictTransform(f::RngMPolLocElt, pi1::RngMPolLocElt, pi2::RngMPolLocElt) -> RngMPolLocElt, RngIntElt, RngIntElt
  {
    Unit part (in the ring of power series in x,y) of the pullback of f(x,y,t1...) by pi=[pi1,pi2] (discarding common powers of x and y), and the discarded powers of x and y
  }
  P := Parent(f);
  x := P.1;
  y := P.2;

  pi_f := Evaluate(f, [pi1, pi2]);
  A := xFactor(pi_f);
  B := yFactor(pi_f);
  u := ExactQuotient(pi_f, x^A*y^B);
  return u, A, B;
end intrinsic;


intrinsic DifferentialFormUnit(pi1::RngMPolLocElt, pi2::RngMPolLocElt) -> RngMPolLocElt
  {
    Unit part of the pullback of the differential form (dx^dy) by pi, discarding common powers of x and y.
    If pi is monomial, the result is 1
  }
  P := Parent(pi1);
  x := P.1;
  y := P.2;
  
  // Pullback of the differential form:
  // dx^dy o pi = d(pi1)^d(pi2)
  // = (d(pi1)/dx * dx + d(pi1)/dy * dy) ^ (d(pi2)/dx * dx + d(pi2)/dy * dy)
  // = d(pi1)/dx * d(pi2)/dy * dx^dy + d(pi1)/dy * d(pi2)/dx * dy^dx
  // = ( d(pi1)/dx * d(pi2)/dy - d(pi1)/dy * d(pi2)/dx ) * dx^dy
  // = Kpi * dx^dy
  // = (x^C * y^D * v) * dx^dy
  Kpi := Derivative(pi1, x) * Derivative(pi2, y) - Derivative(pi1, y) * Derivative(pi2, x); // Jaccobian determinant of the change of variables
  C := xFactor(Kpi); // minimum (common) x exponent in Kpi
  D := yFactor(Kpi); // minimum (common) y exponent in Kpi
  v := ExactQuotient(Kpi, x^C*y^D);
  return v;
end intrinsic;


intrinsic DifferentialFormStrictTransform(v::RngMPolLocElt, pi1::RngMPolLocElt, pi2::RngMPolLocElt) -> RngMPolLocElt
  {
    Unit part of the pullback of the differential form (v * dx^dy) by pi, discarding common powers of x and y.
  }
  return StrictTransform(v, pi1, pi2) * DifferentialFormUnit(pi1, pi2);
end intrinsic;


// Blowup

intrinsic BlowupProjection(n::RngIntElt, q::RngIntElt, xy::[] : choosePi:=1) -> RngMPolLocElt, RngMPolLocElt
  {
    Blowup projection morphism: resolution of the first characteristic exponent q/n of a curve.
    Given as of the two charts containing the exceptional divisor.
    The options include exchanging the order of the morphism's components.
  }
  x, y := Explode(xy);
  
  // gcd(mi,ni)=1 (see PHD-Blanco p.24)
  // qi = mi - ni*m_{i-1} (see PHD-Blanco p.25)
  // => gcd(qi, ni)=1
  _, a, b := Xgcd(-q, n); // solve (-q)*a + n*b = 1 (see TFG_Roger p.20 eq.2.4.10)
  _, c, d := Xgcd(q, -n); // solve q*c + (-n)*d = 1 (see TFG_Roger p.20 eq.2.4.11)
  while (a lt 0 or b lt 0) do a := a + n; b := b + q; end while; // Ensure nonnegative solution
  while (c lt 0 or d lt 0) do c := c + n; d := d + q; end while; // Ensure nonnegative solution
  
  // Choose a blowup morphism
  // Possible morphisms: <x^n*y^a, x^q*y^b> or <x^c*y^n, x^d*y^q> (see TFG_Roger p.20 eq.2.4.10, eq.2.4.11)
  // Options:
  // - charts 1 and 2 cover the whole rupture divisor. Since the curve does not go through 0 or infinity at rupture divisors, both charts are valid blowups.
  // - swap(pi1,pi2) changes which variable is assumed to have power n, such that the blowup works e.g. for y^2-x^3 versus for x^2-y^3
  
  case choosePi:
    when 1:
      pi := <x^n*y^a, x^q*y^b>; // chart 1
    when 2:
      pi := <x^q*y^b, x^n*y^a>; // chart 1, swap(pi1,pi2)
    when 3:
      pi := <x^c*y^n, x^d*y^q>; // chart 2
    when 4:
      pi := <x^d*y^q, x^c*y^n>; // chart 2, swap(pi1,pi2)
  end case;
  pi1, pi2 := Explode(pi);
  return pi1, pi2;
end intrinsic;


intrinsic ChooseBlowupAndTransform(n::RngIntElt, q::RngIntElt, f::RngMPolLocElt, v::RngMPolLocElt, xy::SeqEnum, AB::Tup) -> RngMPolLocElt, RngMPolLocElt, RngMPolLocElt, RngMPolLocElt, RngIntElt, RngIntElt
  {
    Choose adequate blowup morphism and transform f and v accordingly.
    Only works for curves whose free points at non-rupture divisors all lie at the origin (such as those given by the construction at TFG-Roger section 2.4).
  }
  
  // Choose order of preference (1 or 2) for choosing blowup morphisms
  chooseOrder := 1;
  printf "ChooseBlowupAndTransform order: %o\n", chooseOrder;
  case chooseOrder:
    when 1: order := [1,2,3,4]; // Prefer chart 1
    when 2: order := [3,4,1,2]; // Prefer chart 2
  end case;
  
  x, y := Explode(xy);
  oldA, oldB := Explode(AB);
  // Initial total transform: x^oldA * y^oldB * f, f branch
  
  printf "piChoice:\n";
  for piChoice in order do
    printf "%o ", piChoice;
    // Blowup projection morphism
    pi1, pi2 := BlowupProjection(n, q, xy : choosePi:=piChoice);
    //printf "pi = [%o, %o]\n", pi1, pi2;
    
    // Strict transform of f (include x^oldA*y^oldB to correctly calculate the new A and B)
    u, A, B := StrictTransform(x^oldA * y^oldB * f, pi1, pi2);
    //print "A=", A, " B=", B, " u=", u;
    
    // From here on: check requirements for blowup until the next rupture divisor.
    // Break out of for-loop if all requirements are met, else continue to next for-loop iteration to try another blowup morphism
    
    // The rupture divisor is x=0 or y=0 and intersects other exceptional divisors at 0 and infinity => A!=0, B!=0
    // N multiplicity is strictly increasing (see TFG-Roger p.16 Cor.2.3.19 eq.2.3.4, p.13 Prop.2.2.44 eq.2.2.3) => A!=B
    if (A ne 0) and (B ne 0) and (A ne B) then
      
      // For convenience we choose x to be the new rupture divisor <=> x is the divisor with highest multiplicity yet <=> A>B
      if (A lt B) then // Swap the variables x and y
        pi1 := Evaluate(pi1, [y,x]);
        pi2 := Evaluate(pi2, [y,x]);
        u := Evaluate(u, [y,x]);
        A, B := Explode(<B, A>); // Swap A and B (the powers of multiplying x and y)
      end if;
      // Now A>B
      
      // 1) The rupture divisor intersects other exceptional divisors at 0 and infinity
      // 2) The rupture divisor intersects the curve at exactly one different point
      
      // 1+2=>3) The curve does not go through the origin => u(0,0)!=0
      // 1+2=>4) The curve intersects the rupture divisor (not at infinity) => u(0,y) has at least one root => u(0,y) polynomial of degree >=1
      // 2=>5)   The curve intersects the rupture divisor at exactly one point => u(0,y) has exactly 1 root (with some multiplicity)
      
      // 3+4+5<=>6) u(0,y)=coef*(1-mult*y)^exponent, coef!=0, exponent>=1 (=> mult!=0)
      //        <=> coef=u(0,0)!=0, exponent=degree(u(0,y))>=1, MonomialCoefficient(u(0,y),y)=coef*(-mult)*exponent, u(0,y)=coef*(1-mult*y)^exponent
      //        <=> coef=u(0,0)!=0, exponent=degree(u(0,y))>=1, mult=-MonomialCoefficient(u(0,y),y)/(coef*exponent), u(0,y)=coef*(1-mult*y)^exponent
      
      // Observation: 6) => degree(u)>0 => also discards the incorrect case where u=1 because the strict transform is x or y
      
      // Check 6)
      u0 := Evaluate(u,x,0); // u(0,y)
      coef := Evaluate(u0,y,0); // u(0,0)
      if coef ne 0 then
        exponent := Degree(u0,y);
        if exponent ge 1 then
          mult := -MonomialCoefficient(u0,y)/(coef*exponent);
          if u0 eq coef*(1-mult*y)^exponent then
            break; // All requirements for the blowup until the next rupture divisor are met by this blowup morphism
          end if;
        end if;
      end if;
    end if;
    
    error if piChoice eq order[#order], "No blowup found"; // Error if checked all blowup options unsuccessfully
  end for;
  printf "\n";
  
  coef := Evaluate(u, [0,0]); // 6) => coef=u(0,0)!=0
  u /:= coef; // u0 = 1 - lambda*y + ...
  
  // Pullback of differential form (v dx^dy) by pi, ignoring common x and y
  v := DifferentialFormStrictTransform(v, pi1, pi2);

  return pi1, pi2, u, v, A, B;
end intrinsic;


// Other

function EvaluateTup(t, psi)
  // Evaluate at psi each element f=t[i] of the tuple t
  for i->f in t do
    t[i] := Evaluate(f, psi);
  end for;
  return t;
end function;


intrinsic StepByStepBlowup(f::RngMPolLocElt, P::RngMPolLoc, AB::Tup, EPrev::RngMPolLocElt, EProx::RngMPolLocElt, isInStair::BoolElt) -> RngMPolLocElt, RngMPolLocElt, RngMPolLocElt, RngIntElt, RngIntElt
  {
    Choose adequate blowup morphism and transform f and v accordingly.
    f sinularity at (0,0)
    (see TFG-Roger p.59 section 6.6.3, also section 5)
  }
  
  // Choose order of preference (1 or 2) for choosing blowup morphisms
  chooseOrder := 1;
  printf "StepByStepBlowup order: %o\n", chooseOrder;
  
  oldA, oldB := Explode(AB);
  R := BaseRing(P);
  x := P.1;
  y := P.2;
  
  // For convenience we choose E=x to be the new rupture divisor
  
  for j in [1,2] do
    if j eq chooseOrder then
      psi := [x, x*y]; // blowup morphism (first option)
      A, B := Explode(<oldA+oldB, oldB>); // powers of x and y in (psi[1])^oldA*(psi[2])^oldB
    else
      psi := [x*y, x]; // blowup morphism (second option)
      A, B := Explode(<oldA+oldB, oldA>); // powers of x and y in (psi[1])^oldA*(psi[2])^oldB
    end if;
    pi1 := psi[1]; pi2 := psi[2]; // save total transformation
    u, A2, B2 := StrictTransform(f, psi[1], psi[2]); // u = strict transform of f, discard multiplying x^A2 and y^B2
    A +:= A2; // A: total power of x
    B +:= B2; // B: total power of y
    u0 := Evaluate(u, x, 0); // u0 = equation of intersecion of u and E (polynomial in y)
    
    // (0,0) singular, free => u non-unit
    // (0,0) singular, satellite => u != 
    
    // Fix the case where u=y but StrictTransform returns a constant because u=y is a variable.
    // In this case the point is already smooth and free => stop
    if IsUnit(u) then
      u := y;
      printf "psi = [%o, %o]\n", psi[1], psi[2];
      return pi1, pi2, u, A, B-1;
    end if;
    
    if (not IsUnit(u0)) then // u0 has a root => u intersects E in this blowup chart
      break; // Adequate blowup found
    end if;
    // Else: u does not intersect E in this chart, try again with the other blowup morphism
  end for;
  
  printf "psi = [%o, %o]\n", psi[1], psi[2];
  
  // u0 = coef*(y-a)^exponent (see ChooseBlowupAndTransform())
  exponent := Degree(u0, y);
  u0 /:= Coefficient(u0, y, exponent); // remove multiplying constant
  // u0 = (y-a)^exponent = y^exponent - a*exponent*y^(exponent-1) + ...
  a := R ! (- Coefficient(u0, y, exponent-1) / exponent); // coordinate of intersection
  point := [0,a]; // next point
  
  // Check proximity of point (other divisors are proximate if after blowup they contain the next point)
  EPrev, EProx := Explode(EvaluateTup(<EPrev, EProx>, psi)); // (total) transform previous divisors
  EPrev := ExactQuotient(EPrev, x^xFactor(EPrev)); // discard E component
  EProx := ExactQuotient(EProx, x^xFactor(EProx)); // discard E component
  proximate := P!1;
  if Evaluate(EProx, point) eq 0 then
    proximate := EProx;
  elif Evaluate(EPrev, point) eq 0 then
    proximate := EPrev;
  end if;
  isFree := (proximate eq 1);
  
  // Stop if we arrived at a rupture divisor
  if ( isInStair and isFree ) then // (see TFG-Roger p.18 Rk.2.3.26)
    return pi1, pi2, u, A, B;
  end if;
  
  // Re-center the intersection point of E and u to (0,0)
  if a ne 0 then
    psi := [x, y+a];
    u, pi1, pi2, proximate := Explode(EvaluateTup(<u, pi1, pi2, proximate>, psi));
    // E is still x
    B := yFactor(u);
    u := ExactQuotient(u, y^B);
    printf "psi = [%o, %o]\n", psi[1], psi[2];
  end if;
  
  // continue blowup
  isInStair := not isFree;
  pi1next, pi2next, u, Anext, Bnext := StepByStepBlowup(u, P, <A,B>, x, proximate, isInStair);
  pi1, pi2 := Explode(EvaluateTup(<pi1, pi2>, [pi1next, pi2next]));
  return pi1, pi2, u, Anext, Bnext;
end intrinsic;


