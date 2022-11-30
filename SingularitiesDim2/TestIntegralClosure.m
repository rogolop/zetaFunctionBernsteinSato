AttachSpec("./IntegralClosureDim2.spec");
Q<x, y> := LocalPolynomialRing(RationalField(), 2, "lglex");

function GradientIdeal(f)
  return ideal<Q | Derivative(f, 1), Derivative(f, 2)>;
end function;

function JacobianIdeal(f)
  return ideal<Q | f, Derivative(f, 1), Derivative(f, 2)>;
end function;

ConvertToIdeal := func<I, Q | ideal<Q | [&*[g[1]^g[2] : g in f] : f in I]>>;

// Whole ring
I := ideal<Q | y*(1 + x), y*y>;
II := IntegralClosure(I);
assert(#II[1] eq 1);
assert(II[1][1] eq <y, 1>);

print "O";

// Principal ideal
I := ideal<Q | y^2 - x^3>;
II := IntegralClosure(I);
assert(#II[1] eq 1);
assert(II[1][1] eq <y^2 - x^3, 1>);

print "P";

// Maximal ideal
I := ideal<Q | (y^2 - x^3)*x, (y^2 - x^3)*y>;
II := IntegralClosure(I);
assert(#II eq 2);
assert(#II[1] eq 2); f1 := II[1];
assert(#II[2] eq 2); f2 := II[2];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 1>);
assert(f1[2] eq <QQ!(y^2 - x^3), 1>);
assert(f2[1] eq <QQ!y, 1>);
assert(f2[2] eq <QQ!(y^2 - x^3), 1>);

print "m";

// Single free point
I := ideal<Q | y, x^2>;
II0 := IntegralClosure(I);
assert(#II0 eq 2);
assert(#II0[1] eq 1); f1 := II0[1];
assert(#II0[2] eq 1); f2 := II0[2];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!y, 1>);
assert(f2[1] eq <QQ!x, 2>);
I2 := ConvertToIdeal(II0, Q);
assert(I eq I2);

// Single free point
I := ideal<Q | x, y^2>;
II1 := IntegralClosure(I);
assert(#II1 eq 2);
assert(#II1[1] eq 1); f1 := II1[1];
assert(#II1[2] eq 1); f2 := II1[2];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 1>);
assert(f2[1] eq <QQ!y, 2>);
I2 := ConvertToIdeal(II1, Q);
assert(I eq I2);

print "p";

// Cusp ideal
I0 := ideal<Q | y^2, x^3>;
II0 := IntegralClosure(I0);
assert(#II0 eq 3);
assert(#II0[1] eq 1); f1 := II0[1];
assert(#II0[2] eq 1); f2 := II0[2];
assert(#II0[3] eq 2); f3 := II0[3];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!y, 2>);
assert(f2[1] eq <QQ!x, 3>);
assert(f3[1] eq <QQ!y, 1>);
assert(f3[2] eq <QQ!x, 2>);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0); assert(C0 eq Parent(C0)!CC0);

// Cups ideal
I1 := ideal<Q | x^2, y^3>;
II1 := IntegralClosure(I1);
assert(#II1 eq 3);
assert(#II1[1] eq 1); f1 := II1[1];
assert(#II1[2] eq 2); f2 := II1[2];
assert(#II1[3] eq 1); f3 := II1[3];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 2>);
assert(f2[1] eq <QQ!y, 2>);
assert(f2[2] eq <QQ!x, 1>);
assert(f3[1] eq <QQ!y, 3>);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1); assert(C1 eq Parent(C1)!CC1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "cusp";

// Exemple common branch
I0 := ideal<Q | x^2, x*y^2, y^5 - x^6>;
II0 := IntegralClosure(I0);
assert(#II0 eq 3);
assert(#II0[1] eq 2); f1 := II0[1];
assert(#II0[2] eq 1); f2 := II0[2];
assert(#II0[3] eq 1); f3 := II0[3];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!y, 2>);
assert(f1[2] eq <QQ!x, 1>);
assert(f2[1] eq <QQ!y, 5>);
assert(f3[1] eq <QQ!x, 2>);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0); assert(C0 eq Parent(C0)!CC0);

// Exemple common branch
I1 := ideal<Q | y^2, y*x^2, x^5 - y^6>;
II1 := IntegralClosure(I1);
assert(#II1 eq 3);
assert(#II1[1] eq 1); f1 := II1[1];
assert(#II1[2] eq 1); f2 := II1[2];
assert(#II1[3] eq 2); f3 := II1[3];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 5>);
assert(f2[1] eq <QQ!y, 2>);
assert(f3[1] eq <QQ!y, 1>);
assert(f3[2] eq <QQ!x, 2>);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1); assert(C1 eq Parent(C1)!CC1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "common";
//
// Casas' Collectanea example
I0 := ideal<Q | x^5*y - y^3, x^8 + 2*x^5*y>;
II0 := IntegralClosure(I0);
assert(#II0 eq 4);
assert(#II0[1] eq 1); f1 := II0[1];
assert(#II0[2] eq 2); f2 := II0[2];
assert(#II0[3] eq 2); f3 := II0[3];
assert(#II0[4] eq 1); f4 := II0[4];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 8>);
assert(f2[1] eq <QQ!y, 1>);
assert(f2[2] eq <QQ!x, 5>);
assert(f3[1] eq <QQ!y, 2>);
assert(f3[2] eq <QQ!x, 3>);
assert(f4[1] eq <QQ!y, 3>);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0); assert(C0 eq Parent(C0)!CC0);
J0 := ideal<Q | x^5*y - y^3, x*(y^2 - x^5)*(y - x^2), x*y*(y - x^2)^2, x*y^2*(y - x^2)>;
assert(II0 eq J0);

// Casas' Collectanea example
I1 := ideal<Q | y^5*x - x^3, y^8 + 2*y^5*x>;
II1 := IntegralClosure(I1 );
assert(#II1 eq 4);
assert(#II1[1] eq 2); f1 := II1[1];
assert(#II1[2] eq 2); f2 := II1[2];
assert(#II1[3] eq 1); f3 := II1[3];
assert(#II1[4] eq 1); f4 := II1[4];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!y, 5>);
assert(f1[2] eq <QQ!x, 1>);
assert(f2[1] eq <QQ!y, 3>);
assert(f2[2] eq <QQ!x, 2>);
assert(f3[1] eq <QQ!y, 8>);
assert(f4[1] eq <QQ!x, 3>);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1); assert(C1 eq Parent(C1)!CC1);
J1 := ideal<Q | y^5*x - x^3, y*(x^2 - y^5)*(x - y^2), y*x*(x - y^2)^2, y*x^2*(x - y^2)>;
assert(II1 eq J1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "casas";

// A1
f := (y^2 - x^3)*(y^2 + x^3);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 4);
assert(#II0[1] eq 1); f1 := II0[1];
assert(#II0[2] eq 2); f2 := II0[2];
assert(#II0[3] eq 2); f3 := II0[3];
assert(#II0[4] eq 1); f4 := II0[4];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!y, 3>);
assert(f2[1] eq <QQ!y, 1>);
assert(f2[2] eq <QQ!x, 4>);
assert(f3[1] eq <QQ!y, 2>);
assert(f3[2] eq <QQ!x, 2>);
assert(f4[1] eq <QQ!x, 5>);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0); assert(C0 eq Parent(C0)!CC0);

// A1
f := (x^2 - y^3)*(x^2 + y^3);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 4);
assert(#II1[1] eq 1); f1 := II1[1];
assert(#II1[2] eq 2); f2 := II1[2];
assert(#II1[3] eq 2); f3 := II1[3];
assert(#II1[4] eq 1); f4 := II1[4];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 3>);
assert(f2[1] eq <QQ!y, 2>);
assert(f2[2] eq <QQ!x, 2>);
assert(f3[1] eq <QQ!y, 4>);
assert(f3[2] eq <QQ!x, 1>);
assert(f4[1] eq <QQ!y, 5>);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1); assert(C1 eq Parent(C1)!CC1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A1";

// A2
f := (y^2 - x^3)*(y^2 - 2*x^3);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 5);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A2
f := (x^2 - y^3)*(x^2 - 2*y^3);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 5);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A2";

// A3
f := (y^2 - x^3)*((y - x)^2 - x^3);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A3
f := (x^2 - y^3)*((x - y)^2 - y^3);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A3";

// A4
f := y^3 - x^11 + x^8*y;
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(#II0 eq 4);
assert(#JJ0 eq 4);

f := Evaluate(f, <y, x>);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(#II0 eq 4);
assert(#JJ0 eq 4);

print "A4";

// A5
f := y^3 - x^11;
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 3);
assert(#II0[1] eq 1); f1 := II0[1];
assert(#II0[2] eq 2); f2 := II0[2];
assert(#II0[3] eq 1); f3 := II0[3];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!x, 10>);
assert(f2[1] eq <QQ!y, 1>);
assert(f2[2] eq <QQ!x, 5>);
assert(f3[1] eq <QQ!y, 2>);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A5
f := x^3 - y^11;
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 3);
assert(#II1[1] eq 2); f1 := II1[1];
assert(#II1[2] eq 1); f2 := II1[2];
assert(#II1[3] eq 1); f3 := II1[3];
QQ := Parent(f1[1][1]);
assert(f1[1] eq <QQ!y, 5>);
assert(f1[2] eq <QQ!x, 1>);
assert(f2[1] eq <QQ!y, 10>);
assert(f3[1] eq <QQ!x, 2>);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A5";

// A6
f := (y^5 - x^3)*(y^3 - x^5);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 6);
assert(#II0[1] eq 2);
assert(#II0[2] eq 2);
assert(#II0[3] eq 2);
assert(#II0[4] eq 2);
assert(#II0[5] eq 1);
assert(#II0[6] eq 1);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A6
f := (x^5 - y^3)*(x^3 - y^5);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 6);
assert(#II1[1] eq 2);
assert(#II1[2] eq 2);
assert(#II1[3] eq 2);
assert(#II1[4] eq 2);
assert(#II1[5] eq 1);
assert(#II1[6] eq 1);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A6";

// A7
f := (x^2 - y)*(x^2 + y)*(x - y^2)*(x + y^2)*(x^2 - (x - y))*(x^2 + (x - y));
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 8);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);

// A7
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 8);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);

print "A7";

// A8
f := y^3 - x^10;
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 3);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A8
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 3);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A8";

// A9
f := y*(y^2 - x^3);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 4);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A9
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 4);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A9";

// A10
f := y*(y^2 - x^3)*(y - x^2);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 5);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A10
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 5);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);

print "A10";

// A11
f := y*(y^2 - x^3)*(y - x^2)*(y - x^3);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 7);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);

// A11
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 7);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);

print "A11";

// A12
f := (y^2 - x^3)*(y^2 - x^5);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 5);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);
//assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A12
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 5);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);
//assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);

print "A12";

// A13
f := y*(y^2 - x^3)*(y^2 - x^5);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 7);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A13
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 7);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A13";

// A14
f := (y^3 - x^5)*((y- x^2)^3 - x^5);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 7);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A14
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 7);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A14";

// A15
f := y*(y - x^2)*(y + x^2);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(#II0 eq 4 and #JJ0 eq 4);

// A15
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(#II1 eq 4 and #JJ1 eq 4);

print "A15";

// A16
f := y*(y - x^2)*(y + x^2)*(y^3 - x^5)*((y - x^2)^3 - x^5);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(#II0 eq 15 and #JJ0 eq 15);

// A16
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(#II1 eq 15 and #JJ1 eq 15);

print "A16";

// A18
f := y^7 - x^16;
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 7);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A18
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 7);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A18";

// A19
f := y^10 - x^23;
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 10);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A19
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 10);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A19";

// A20
f := (y - x)*(y^2 - x^3)*(x^2 - y^3);
I0 := GradientIdeal(f); II0 := IntegralClosure(I0);
J0 := JacobianIdeal(f); JJ0 := IntegralClosure(J0);
assert(ConvertToIdeal(JJ0, Q) eq ConvertToIdeal(II0, Q));
assert(#II0 eq 5);
II0 := ConvertToIdeal(II0, Q);
B0 := BasePoints(I0 : Coefficients := true);
P0 := B0[1]; v0 := B0[2]; g0 := B0[3]; C0 := B0[4];
BB0 := BasePoints(II0 : Coefficients := true);
PP0 := BB0[1]; vv0 := BB0[2]; gg0 := BB0[3]; CC0 := BB0[4];
assert(Ncols(P0) eq Ncols(PP0)); assert(g0 eq gg0);
assert(P0 eq PP0); assert(v0 eq vv0); assert(g0 eq gg0);

// A19
f := Evaluate(f, <y, x>);
I1 := GradientIdeal(f); II1 := IntegralClosure(I1);
J1 := JacobianIdeal(f); JJ1 := IntegralClosure(J1);
assert(ConvertToIdeal(JJ1, Q) eq ConvertToIdeal(II1, Q));
assert(#II1 eq 5);
II1 := ConvertToIdeal(II1, Q);
B1 := BasePoints(I1 : Coefficients := true);
P1 := B1[1]; v1 := B1[2]; g1 := B1[3]; C1 := B1[4];
BB1 := BasePoints(II1 : Coefficients := true);
PP1 := BB1[1]; vv1 := BB1[2]; gg1 := BB1[3]; CC1 := BB1[4];
assert(Ncols(P1) eq Ncols(PP1)); assert(g1 eq gg1);
assert(P1 eq PP1); assert(v1 eq vv1); assert(g1 eq gg1);

assert(II0 eq ideal<Q | [Evaluate(f, <y, x>) : f in Basis(II1)]>);
assert(Ncols(P0) eq Ncols(P1)); assert(g0 eq g1);
assert(Ncols(PP0) eq Ncols(PP1)); assert(gg0 eq gg1);
assert(P0 eq P1); assert(v0 eq v1); assert(g0 eq g1);
assert(PP0 eq PP1); assert(vv0 eq vv1); assert(gg0 eq gg1);

print "A20";
