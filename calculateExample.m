AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("ZetaFunction/ZetaFunction.spec");
Z := IntegerRing();
Q := RationalField();

P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 4), 2);
R<t0,t1,t2,t17> := BaseRing(P);
assumeNonzero:={R| t0};
f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0)^2 + (-x^7 + y^3)^2;
// f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0)^2 + (-x^7 + t1*x^5*y + t2*x^3*y^2 + y^3)^2;

//P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 6), 2);
//R<A_43,A_34,A_44,A_52,A_53,A_54> := BaseRing(P);
//f := y^6 - x^7 + A_52*x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4 + A_53*x^5*y^3 + A_54*x^5*y^4;

//P<x,y> := LocalPolynomialRing(RationalFunctionField(Q, 18), 2);
//R<t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17> := BaseRing(P);
//invertibleVariables:=[Z| 1];
//f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0 + t3*x + t6*x^2 + t9*x^3 + t11*x^4 + t13*x^5 + t7*y + t10*x*y + t12*x^2*y + t14*x^3*y + t15*x^4*y + t16*x^5*y)^2 + (-x^7 + t1*x^5*y + t4*x^6*y + t2*x^3*y^2 + t5*x^4*y^2 + t8*x^5*y^2 + y^3)^2;

L_all, sigma_all := ZetaFunctionStratificationDefault( f :
	assumeNonzero:=assumeNonzero,
	verboseLevel:="default"
	);

printf "Finished\n";
quit;

