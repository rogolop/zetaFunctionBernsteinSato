AttachSpec("./IntegralClosureDim2.spec");
Q<x, y> := LocalPolynomialRing(RationalField(), 2, "lglex");

function ConvertToIdeal(I, Q)
  return ideal<Q | [&*[f_i[1]^f_i[2] : f_i in f] : f in I]>;
end function;

// Casas' book example.
book := y^4 - x^2*y^2 - 2*x^4*y^2 + x^4*y + x^5*y + x^7;

// email examples.
aa := y^4 - 2*x^3*y^2 + x^6 - 4*x^10*y - x^17;
bb := x^4 - 2*x^2*y^5 - 4*x*y^8 + y^10 - y^11;
bbb := -x^11 + x^10 - 4*y*x^8 - 2*y^2*x^5 + y^4;
cc := y^4 - 2*x^3*y^2 + x^6 - 4*x^9*y - x^15;

ee := bb^2 + x^10;
ff := bbb^2 + y^10;

gg := bb^2 + x^11;
jj := bbb^2 + y^11;

mm := bb^3 + x^13; // 3 char exponents
ll := bbb^3 + y^13; // 3 char exponents

// singular examples.
f1 := (y^2-x^3)^2-4*x^5*y-x^7;
f2 := y^2-x^3;
f3 := y^3-x^2;

// other examples.
f := y^3 + x^2*y^2 + x^6;
g := x^3 + x^2*y^2 + y^6;
h := x^5+y^5;
foo := x+y;
bar := y*(x+y);

// Victor's Thesis examples.
v1 := (y^2 - x^3)*(y^2 + x^3);
v2 := (y^2 - x^3)*(y^2 - 2*x^3);
v3 := (y^2 - x^3)*((y - x)^2 - x^3);
v4 := y^3 - x^11 + x^8*y;
v5 := y^3 - x^11;
v6 := (y^5 - x^3)*(y^3 - x^5);
v7 := (x^2 - y)*(x^2 + y)*(x - y^2)*(x + y^2)*(x^2 - (x - y))*(x^2 + (x - y));
v8 := y^3 - x^10;
v9 := y*(y^2 - x^3);
v10 := y*(y - x^2)*(y^2 - x^3);
v11 := y*(y - x^2)*(y - x^3)*(y^2 - x^3);
v12 := (y^2 - x^3)*(y^2 - x^5);
v13 := y*(y^2 - x^3)*(y^2 - x^5);
v14 := (y^3 - x^5)*((y - x^2)^3 - x^5); // Wrong!
v15 := y*(y - x^2)*(y + x^2);
v16 := y*(y - x^2)*(y + x^2)*(y^3 - x^5)*((y - x^2)^3 - x^5); // Wrong!
v17 := &*[y^4 - k*x^7 : k in [1..7]];
v18 := y^7 - x^16;
v19 := y^10 - x^23;
v20 := (y - x)*(y^2 - x^3)*(x^2 - y^3);
vA := (y^4 - x^11)*(y^3 - x^8)*(y^9 - x^22)*(y^12 - x^29)*(y^4 - x^9);
vB := (y^5 - x^8)*(y^4 - 4*x^2*y^3 + 6*x^4*y^2 - 4*x^6*y - x^7 + x^8)*(y^16 - 4*x^7*y^12 + 6*x^14*y^8 - 80*x^14*y^9 - 4*x^21*y^4 - 160*x^21*y^5 - 72*x^21*y^6 + x^28 - 16*x^28*y + 56*x^28*y^2 - 16*x^28*y^3 - x^35)*(y^20 - 5*x^7*y^16 + 10*x^14*y^12 - 60*x^14*y^13 - 10*x^21*y^8 - 540*x^21*y^9 - 2*x^21*y^10 + 5*x^28*y^4 - 404*x^28*y^5 + 380*x^28*y^5 - x^35 - 20*x^35*y - 90*x^35*y^2 - 40*x^35*y^3 + x^42);
vC := (y^3 - x^8)*(y^4 - x^9)*(y^7 - x^16)*(y^16 - 4*x^11*y^12 - 80*x^21*y^9 + 6*x^22*y^8 - 72*x^31*y^6 - 160*x^32*y^5 - 4*x^33*y^4 - 16*x^41*y^3 + 56*x^42*y^2 - 16*x^43*y + x^44 - x^51)*(y^20 - 5*x^11*y^16 + 10*x^22*y^12 - 140*x^24*y^12 - 10*x^33*y^8 - 620*x^35*y^8 - 110*x^37*y^8 + 5*x^44*y^4 - 260*x^46*y^4 + 340*x^48*y^4 - 20*x^50*y^4 - x^55 - 4*x^57 - 6*x^59 - 4*x^61 - x^63);

// Ideals

I0 := ideal<Q | x^5*y - y^3, x^8 + 2*x^5*y>;
II0 := ideal<Q | x^5*y - y^3, x*(y^2 - x^5)*(y - x^2), x*y*(y - x^2)^2, x*y^2*(y - x^2)>;

I1 := ideal<Q | Derivative(v1, 1), Derivative(v1, 2)>;
II1 := ideal<Q | y^3 - x^5, (y^2 - x^3)*x^2, y^2*x^2, (y^2 - x^3)*x*y>;

I2 := ideal<Q | Derivative(v2, 1), Derivative(v2, 2)>;
II2 := ideal<Q | y*(y^2 - 3/2*x^3), (y^2 - x^3)*x^2, y^2*x^2, (y^2 - x^3)*x*y>;
