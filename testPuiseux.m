AttachSpec("./SingularitiesDim2/IntegralClosureDim2.spec");

function SerToPol(s, R)
  C, v, d := Coefficients(s);
  P := PolynomialRing(R);
  pol := P ! Coefficients(s);
  pol *:= (P.1)^v;
  return pol;
end function;

function DiscardHigherPow(f, var, pow)
  return &+[Parent(f) | t : t in Terms(f) | Degree(t, var) le pow];
end function;

Q := RationalField();
P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
R<t1,t2,t6,t10> := BaseRing(P);

f := t1*x - t2*x^2 + y - t1*x*y + 2*t2*x^2*y - t2*x^2*y^2;

M := 5; // Max order in x

// Puiseux

zM := PuiseuxExpansionReduced(f : Terms:=M)[1];

z := PuiseuxExpansionReduced(f : Terms:=1)[1];
for i in [2..M] do
     z := PuiseuxExpansionExpandReduced(z, f)[1];
end for;

zM := Evaluate(SerToPol(zM, R), x);
z := Evaluate(SerToPol(z, R), x);

printf "M = %o\n\n", M;
printf "zM(x) = %o + O(x^(M+1))\n\n", zM;
printf "z(x)  = %o + O(x^(M+1))\n\n", z;

printf "---> z and zM should be the same, z wrong (???)\n\n";

// Evaluate f

printf "f(x,zM(x)) = %o + O(x^(M+1))\n\n", DiscardHigherPow( Evaluate(f, y, zM), x, 5);
printf "f(x,z(x) ) = %o + O(x^(M+1))\n\n", DiscardHigherPow( Evaluate(f, y, z ), x, 5);

printf "---> f(x,zM) should be the same, both 0 (???)\n\n";

