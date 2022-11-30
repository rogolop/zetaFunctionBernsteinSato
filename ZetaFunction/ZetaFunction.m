/*
  Author: Roger Gomez Lopez
  
  Formal derivatives, residues of the complex zeta function, helping functions for the changes of variable
*/

// Formal derivatives

intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], xi::RngMPolLocElt) -> SeqEnum, SetEnum
  {
    Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to xi.
    
    F       : sequence of sequences m times, where F[a1,...,am] represents the
              coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...).
    indexsF : nonzero elements of F.
    g       : sequence of functions [g1,...,gm] of (x1,...).
    xi      : derive with respect to xi.
  }
  m := #g;
  DiF := [];
  indexsDiF := indexsF;
  
  // Derivate
  for a in indexsF do
    value := Derivative(SeqElt(F,a),1,xi);
    AssignSeqElt(~DiF, a, value);
  end for;
  
  for a in indexsF do
    for L in [1 .. m] do
      b := a;
      b[L] +:= 1;
      value := SeqElt(F,a) * Derivative(g[L],1,xi);
      PlusAssignSeqElt(~DiF, b, value);
      Include(~indexsDiF, b);
    end for;
  end for;
  
  // Remove zeros
  for a in indexsDiF do
    if SeqElt(DiF,a) eq 0 then
      UndefineSeqElt(~DiF, a);
      Exclude(~indexsDiF, a);
    end if;
  end for;
  
  return DiF, indexsDiF;
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], i::RngIntElt) -> SeqEnum, SetEnum
  {
    Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to xi.
    
    F       : sequence of sequences m times, where F[a1,...,am] represents the
              coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...).
    indexsF : nonzero elements of F.
    g       : sequence of functions [g1,...,gm] of (x1,...).
    i       : derive with respect to the i-th variable.
  }
  return FormalDerivative(F, indexsF, g, Universe(g).i);
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, xi::RngMPolLocElt) -> SeqEnum, SetEnum
  {
    Derivative of (F o g), k times with respect to xi
  }
  for j in [1..k] do
    F, indexsF := FormalDerivative(F, indexsF, g, xi);
  end for;
  return F, indexsF;
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, i::RngIntElt) -> SeqEnum, SetEnum
  {
    Derivative of (F o g), k times with respect to the i-th variable
  }
  return FormalDerivative(F, indexsF, g, k, Universe(g).i);
end intrinsic;


intrinsic FormalDerivative(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], L::SeqEnum[Tup]) -> SeqEnum, SetEnum
  {
    L = Set( <k_1,i_1>, ..., <k_n,i_n> )
      or
    L = Set( <k_1,x_i_1>, ..., <k_n,x_i_n> ).
    Derivate of (F o g) with respect to x_i, k times, for all <k,x_i> in L
  }
  if #L gt 0 then
    k, v := Explode(L[1]);
    require Type(k) eq RngIntElt and (Type(v) eq RngMPolLocElt or Type(v) eq RngIntElt) : "Bad argument types inside tuples of L\nArgument types given:", Type(k), ",", Type(v);
  end if;
  
  for t in L do
    k, v := Explode(t);
    F, indexsF := FormalDerivative(F, indexsF, g, k, v);
  end for;
  return F, indexsF;
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, xi::RngMPolLocElt, discard::SeqEnum) -> SeqEnum, SetEnum
  {
    Derivative of (F o g), k times with respect to xi.
    Discard terms with powers higher than x_discardVar^discardPow at the result
  }
  discardVar, discardPow := Explode(discard);
  Z := IntegerRing();
  if #indexsF gt 0 then
    P := Parent(SeqElt(F,Rep(indexsF)));
  end if;
  
  // Truncate polynomials at x_discardVar^m where m is too high
  for I in indexsF do
    AssignSeqElt(~F, I,  &+[P | t : t in Terms(SeqElt(F,I)) | Degree(t,discardVar) le (k+discardPow)]);
  end for;
  
  // Derivate k times, truncating high powers
  for j in [1..k] do
    // Derivate once
    F, indexsF := FormalDerivative(F, indexsF, g, xi);
    // Truncate polynomials at x_discardVar^m where m is too high
    for I in indexsF do
      AssignSeqElt(~F, I,  &+[P | t : t in Terms(SeqElt(F,I)) | Degree(t,discardVar) le (k-j+discardPow)]);
    end for;
  end for;
  
  return F, indexsF;
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], k::RngIntElt, i::RngIntElt, discard::SeqEnum) -> SeqEnum, SetEnum
  {
    Derivative of (F o g), k times with respect to the i-th variable.
    Discard polynomials that will result in x_discardVar^discardPow*(...) at the result
  }
  return FormalDerivativeDiscardingVar(F, indexsF, g, k, Universe(g).i, discard);
end intrinsic;


intrinsic FormalDerivativeDiscardingVar(F::SeqEnum, indexsF::SetEnum, g::SeqEnum[RngMPolLocElt], L::SeqEnum[Tup], discard::SeqEnum) -> SeqEnum, SetEnum
  {
    L = Set( <k_1,i_1>, ..., <k_n,i_n> )
      or
    L = Set( <k_1,x_i_1>, ..., <k_n,x_i_n> ).
    Derivate of (F o g) with respect to x_i, k times, for all <k,x_i> in L.
    Discard polynomials that will result in x_discardVar^discardPow*(...) at the result
  }
  if #L gt 0 then
    k, v := Explode(L[1]);
    require Type(k) eq RngIntElt and (Type(v) eq RngMPolLocElt or Type(v) eq RngIntElt) : "Bad argument types inside tuples of L\nArgument types given:", Type(k), ",", Type(v);
  end if;
  
  for t in L do
    k, v := Explode(t);
    F, indexsF := FormalDerivativeDiscardingVar(F, indexsF, g, k, v, discard);
  end for;
  return F, indexsF;
end intrinsic;


// Residues

function between0and1(x)
  // return r in the interval (0,1] differing from x in an integer value
  r := x - Floor(x);
  if (r eq 0) then return 1; end if;
  return r;
end function;


function GammaFromTo_Risky(f, t)
  // GammaFromTo(f, t) = Gamma(f) / Gamma(t)
  // Don't avoid zeros and infinities, may cause errors.
  // (f-t) must be integer
  error if ((f-t) notin IntegerRing()), "At GammaFromTo(f, t): f and t must differ by an integer\nGiven arguments:", f, ",", t;
  
  coef := 1;
  
  while (f gt t) do
    f -:= 1;    
    coef *:= f;
  end while;
  
  while (f lt t) do
    coef /:= f;
    f +:= 1;
  end while;
  
  return coef;
end function;


intrinsic E(l::RngIntElt, k::RngIntElt, epsilon::[], ep::RngIntElt) -> FldFunRatMElt
  {
    Gamma(l+epsilon+1) * Gamma(sigma-i+1) / Gamma(l+epsilon+sigma-i+2) * 1/ref, with ref = Gamma(a) * Gamma(b) / Gamma(c), where a,b,c are in the interval (0,1] differing of the first values by integer numbers.
  }
  e := 1;
  
  arg := epsilon[1] + 1 + l;
  e *:= GammaFromTo_Risky(arg, between0and1(arg));
  //e *:= GammaFromTo_Risky(arg, epsilon[1] + 1);
  
  arg := epsilon[3] + 1 - ep*k;
  e *:= GammaFromTo_Risky(arg, between0and1(arg));
  //e *:= GammaFromTo_Risky(arg, epsilon[3] + 1);
  
  arg := epsilon[1] + epsilon[3] + 2 + l - ep*k;
  e /:= GammaFromTo_Risky(arg, between0and1(arg));
  //e /:= GammaFromTo_Risky(arg, epsilon[1] + epsilon[3] + 2 ); 
  return e;
end intrinsic;


intrinsic SeparateYTerms(s::SeqEnum, indexs::SetEnum) -> SeqEnum
  {
    Convert each polynomial in s to a sequence of pairs [l,term], there term is the coefficient of y^l of the polynomial (as member of R[y] with the corresponding ring R)
  }  
  function listYTerms(f)
    L := [];
    for l in [0..Degree(f,2)] do
      term := Coefficient(f, 2, l);
      if term ne 0 then
        Append(~L, <l, term>);
      end if;
    end for;
    return L;
  end function;
  
  w := [];
  for I in indexs do
    AssignSeqElt(~w, I, listYTerms(SeqElt(s, I)));
  end for;
  
  return w;
end intrinsic;


function FallingFactorial(n, k)
  return &*[Parent(n) | (n-i) : i in [0..k-1]];
end function;


intrinsic nonconjugateResidue(DPhi_terms::SeqEnum, indexs_DPhi::SetEnum, sigma::FldRatElt, lambda::FldElt, epsilon::[], ep::RngIntElt) -> SeqEnum, SetEnum
  {
    "Nonconjugate" part of the residue of the complex zeta function, with indexing representing the derivatives of delta(x,y). Multiply the result by its conjugate to obtain the full residue (apart from the multiplying constant).
  }
  Res := [];
  indexs_Res := {};
  
  for ijk in indexs_DPhi do
    ij := ijk[1..2]; // numbers of derivatives of delta distribution (+1: kept as indexs)
    k := ijk[3]-1; // number of derivatives of u^s
    
    // Integrate
    pijk_seq := SeqElt(DPhi_terms, ijk);
    res := 0;
    for pair in pijk_seq do
      l, pijkl := Explode(pair);
      // Add term to the residue
      res +:= pijkl * lambda^(-l) * E(l, k, epsilon, ep);
    end for;
    PlusAssignSeqElt(~Res, ~indexs_Res, ij, res);
  end for;
  
  // Remove zeros
  for ij in indexs_Res do
    if SeqElt(Res, ij) eq 0 then
      Exclude(~indexs_Res, ij);
    end if;
  end for;
  return Res, indexs_Res;
end intrinsic;


intrinsic FactorizedBasis(Res::[], indexs_Res::{}, P::RngMPolLoc) -> []
  {
    Get a simplified basis of polynomials, as sequences of factors without multiplicity, without denominators
  }
  R := BaseRing(P);
  
  // Ignore which (derivative of) delta-function they multiply. Each polynimial multiplies to a different delta-function, so the residue is only 0 at common roots of all polynomials.
  // Coerce into a nonlocal polynomial ring for the function Reduce()
  listRes := [R | SeqElt(Res, ij) : ij in indexs_Res ];
  
  // If the residue is the constant 0 (listRes is [])
  if #listRes eq 0 then
    return [[R|0]]; // Return the polynomial 0 for clarity
  end if;
  
  if (Type(R) eq FldFunRat) then
    Rpol := Parent(Numerator(R!1));
    listRes := [Rpol | Numerator(elt) : elt in listRes];
    listRes := Reduce(listRes);
  else
    if (#[R | elt : elt in listRes | IsUnit(elt)] gt 0) then
      listRes := [1];
    end if;
  end if;
  
  // If the residue never vanishes (has a nonzero constant term)
  if listRes eq [1] then 
    return [[R|1]]; // Return the polynomial 1 for clarity
  end if;
  
  // If the execution arrives here, listRes is a nonempty list of nonconstant polynomials. Then separate the factors and clear coefficient denominators (multiplicative constants don't affect zeros)
  if (Type(R) eq FldFunRat) then
    L := [ [R | ClearDenominators(tup[1]) : tup in Factorization(g)] : g in listRes];
  else
    L := [ [R | g] : g in listRes];
  end if;
  
  //L := [[p]: p in listRes];
  return L;
end intrinsic;


intrinsic PrintStratification(L::[[]], nu, sigma, Np)
  {
    print [[]] containing the polynomials where a residue is 0
  }
  printf "%4o │ %4o/%-4o = %8o ", nu, (sigma*Np), Np, sigma;
  if L eq [[0]] then
    printf "[ 0";
  elif L eq [[1]] then
    printf "[   1";
  elif #L eq 1 then
    l := L[1];
    printf "─"^1*" ";
    for j->f in l do
      printf "(%o)", f;
      if j lt #l then printf " or "; end if;
    end for;
  else
    printf "─"^0*"┬ ";
    for i->l in L do
      for j->f in l do
        printf "(%o)", f;
        if j lt #l then printf " or "; end if;
      end for;
      if i lt #L then
        printf "\n"*" "^5*"│"*" "^22*" "^0;
        if i eq (#L-1) then
          printf "└";
        else
          printf "│";
        end if;
        printf " ";//*"& ";
      end if;
    end for;
  end if;
  printf "\n";
end intrinsic;


intrinsic PrintStratificationAsCSV(L::[[]], nu, sigma, Np)
  {
    print [[]] containing the polynomials where a residue is 0
  }
  printf "%4o, %4o/%-4o, %8o, ", nu, (sigma*Np), Np, sigma;
  if L eq [[0]] then
    printf "0";
  elif L eq [[1]] then
    printf "1";
  elif #L eq 1 then
    l := L[1];
    for j->f in l do
      printf "%o", f;
      if j lt #l then printf ", "; end if;
    end for;
  else
    for i->l in L do
      for j->f in l do
        printf "%o", f;
        if j lt #l then printf ", "; end if;
      end for;
      if i lt #L then
        //printf "\n%4o, %4o/%-4o, %8o, ", nu, (sigma*Np), Np, sigma;
        printf "\n,,, ";
      end if;
    end for;
  end if;
  printf "\n";
end intrinsic;


intrinsic PrintStratificationAsLatex(L::[[]], nu, sigma, Np)
  {
    print [[]] containing the polynomials where a residue is 0
  }
  printf "        $%4o $&$ %4o/%-4o =  %8o $&$ ", nu, (sigma*Np), Np, sigma;
  if L eq [[0]] then
    printf "0";
  elif L eq [[1]] then
    printf "1";
  elif #L eq 1 then
    l := L[1];
    for j->f in l do
      sf := Sprint(f);
      //str := (sf[1] eq "t") select "t_" else "";
      //str cat:= &cat[ part cat "t_" : part in Split(sf,"t")];
      str := &cat[ part cat "\\," : part in Split(sf,"*")];
      str := Substring(str, 1, #str-2);
      printf "%o", str;
      if j lt #l then printf "$,$ "; end if;
    end for;
  else
    for i->l in L do
      for j->f in l do
        sf := Sprint(f);
        //str := (sf[1] eq "t") select "t_" else "";
        //str cat:= &cat[ part cat "t_" : part in Split(sf,"t")];
        str := &cat[ part cat "\\," : part in Split(sf,"*")];
        str := Substring(str, 1, #str-2);
        printf "%o", str;
        if j lt #l then printf "$, $ "; end if;
      end for;
      if i lt #L then
        printf "$\\\\ \n               &                         &$ ";
      end if;
    end for;
  end if;
  printf "$\\\\ \\hline  \n";
end intrinsic;


intrinsic ZetaFunctionResidue(arguments::Tup : printType:="none") -> List, List, List, RngMPolLocElt, RngMPolLocElt
  {
    Return and print stratification of the residue of the complez zeta function at candidate poles corresponding to nus in rupture divisor r, each one as [[]] which is a sequence of generators of the zero ideal, represented as sequences containing their irreducible factors
  }
  
  print "-----------------------------------------------------------------------";
  print "ZetaFunctionResidue";
  //printf "arguments: %o\n\n", arguments;
  
  // Prepare arguments
  P, xy, pi1, pi2, u, v, Np, kp, N, k, nus, r := Explode(arguments);

  x, y := Explode(xy);
  R := BaseRing(P);
  u /:= Evaluate(u, [0,0]);
  
  // Lambda
  u0 := Evaluate(u, x, 0); // (1-lambda*y)^ep = 1-(lambda*ep)*y+...
  ep := Degree(u0, y);
  lambda := R ! - Coefficient(u0,y,1) / ep;
  
  // Formal v(x,y) * phi(X,Y) * Z^s, to be evaluated at X=pi1, Y=pi2, Z=u
  Phi := [[[v]]];
  indexs_Phi := {[1,1,1]};

  // Storage
  L_all := [**];
  sigma_all := [**];
  epsilon_all := [**];
  
  // print stratification table head
  if (#nus gt 0) then
    if (printType eq "table") then
      printf " nu  │         sigma        │ Conditions for residue =0\n";
      printf "─"^5*"┼";
      printf "─"^22*"┼";
      printf "─"^26*"\n";
    elif (printType eq "CSV") then
      printf "nu, sigma, sigma, Conditions for residue =0\n";
    elif (printType eq "Latex") then
      printf "        $\\nu$&$\\sigma_{%o,\\nu}$&Conditions for $\\Ress{\\sigma_{%o,\\nu}}=0$\\\\", r, r;
      printf "\\hline\\hline\n";
    end if;
  end if;
  
  nuMax := Max([0] cat nus); // 0 to avoid errors if nus=[]
  nuOld := 0;
  
  for nu in nus do
    repeat // Do once, but group statements to calculate time easily
      // Relevant numbers
      sigma := Sigma(Np, kp, nu);
      epsilon := [N[j] * sigma + k[j] : j in [1..3] ];
      
      // Derivative of Phi(pi1(...),pi2(...),u(...); x,y) with respect to x
      Phi, indexs_Phi := FormalDerivativeDiscardingVar(Phi, indexs_Phi, [pi1, pi2, u], nu-nuOld, x, [1, nuMax-nu]);
      nuOld := nu;
      
      DPhi := Phi;
      indexs_DPhi := indexs_Phi;
      // Evaluate at x=0
      EvaluateSeq(~DPhi, ~indexs_DPhi, x, 0);
      
      // Convert d^i/dx^i(Z^s) = (s)*...*(s-i+1)*Z^(s-i)
      for ijk in indexs_DPhi do
        k_idx := ijk[3] - 1; // Number of derivatives of Z^s
        TimesAssignSeqElt(~DPhi, ijk, FallingFactorial(sigma, k_idx));
      end for;
            
      // Expand polynomials depending on power of y
      DPhi_terms := SeparateYTerms(DPhi, indexs_DPhi);
      
      // Calculate residue
      Res, indexs_Res := nonconjugateResidue(DPhi_terms, indexs_DPhi, sigma, lambda, epsilon, ep);
      
      // Basis of the ideal whose roots make the residue =0
      L := FactorizedBasis(Res, indexs_Res, P);

      // Storage
      Append(~L_all, L);
      Append(~sigma_all, sigma);
      Append(~epsilon_all, epsilon);
      
      // print
      if (printType eq "table") then
        PrintStratification(L, nu, sigma, Np);
      elif (printType eq "CSV") then
        PrintStratificationAsCSV(L, nu, sigma, Np);
      elif (printType eq "Latex") then
        PrintStratificationAsLatex(L, nu, sigma, Np);
      end if;
    until true;
  end for;
  
  if (printType ne "none") then
    printf "\n";
  end if;

  return L_all, sigma_all, epsilon_all, lambda;
end intrinsic;


// Changes of variables

intrinsic DiscardHigherPow(f, var, pow::RngIntElt) -> Any
  {
    Discard terms with powers of var higher than var^pow
  }
  return &+[Parent(f) | t : t in Terms(f) | Degree(t, var) le pow];
end intrinsic;


intrinsic Evaluate(f::FldFunRatMElt, i::RngIntElt, r::RngElt) -> FldFunRatMElt
  {
    Evaluate a multivariate rational function in x_i=r
  }
  return Evaluate(Numerator(f), i, r) / Evaluate(Denominator(f), i, r);
end intrinsic;


intrinsic MultiplicativeInverse(u::RngMPolLocElt, i::RngIntElt, N::RngIntElt) -> RngMPolLocElt
  {
    Returns the multiplicative inverse of the unit u(x_i), with respect to the i-th variable, up to order N
    u(x_i) must have an invertible x_i^0 coefficient
  }
  P := Parent(u);
  g := Rank(P);
  xi := P.i;
  
  u0 := Coefficient(u,i,0);
  require IsUnit(u0) : "At MultiplicationInverse(u,i,N): u0 is not invertible: u =", u, ", i =", i, ", N =", N, "\nResulting u0: ", u0;

  v := 1/u0;
  for j in [1..N] do
    v -:= xi^j * &+[(Coefficient(u,i,k)*Coefficient(v,i,j-k))/u0 : k in [1..j]];
  end for;
  
  return v;
end intrinsic;


intrinsic SerToPol(s::RngSerPuisElt, R::Rng) -> RngUPolElt
  {
    Convert truncated infinite series to polynomial
  }
  C, v, d := Coefficients(s);
  require d eq 1: "At SeriesToPolynomial(s): The series has fractionary exponents.\nGiven series:", s;
  require v ge 0: "At SeriesToPolynomial(s): The series has negative exponents.\nGiven series:", s;
  P := PolynomialRing(R);
  pol := P ! Coefficients(s);
  pol *:= (P.1)^v;
  return pol;
end intrinsic;
