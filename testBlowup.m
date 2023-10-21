
// units_f, units_w: multiset of terms with multiplicity
// point types: 0 -> start, 1 -> free, 2 -> satellite


AttachSpec("./ZetaFunction/ZetaFunction.spec");
AttachSpec("./SingularitiesDim2/IntegralClosureDim2.spec");
Attach("SingularitiesDim2Extended.m");

Q := RationalField();
P<x,y> := LocalPolynomialRing(Q, 2);


// function xFactor(f)
// 	// minimum (common) x exponent in f (with f != 0)
// 	return Min([IntegerRing() | Exponents(term)[1] : term in Terms(f)]);
// end function;


// function yFactor(f)
// 	// minimum (common) y exponent in f (with f != 0)
// 	return Min([IntegerRing() | Exponents(term)[2] : term in Terms(f)]);
// end function;


// function strictPart(f)
// 	P := Parent(f); x := P.1; y := P.2;
	
// 	A := xFactor(f);
// 	B := yFactor(f);
// 	return ExactQuotient(f, x^A*y^B), A, B;
// end function;


// // Terms of lowest degree of a multivariate polynomial (with no factors x, y)
// function TangentTerm(f)
// 	P := Parent(f); x := P.1; y := P.2;
	
// 	// f := strictPart(f);
// 	assert f eq strictPart(f);
	
// 	ms := Monomials(f);
// 	tan := 0;
// 	min_deg := Infinity();
// 	for m in ms do
// 		deg := Degree(m);
// 		if deg lt min_deg then
// 			min_deg := deg;
// 			tan := MonomialCoefficient(f, m) * m;
// 		elif deg eq min_deg then
// 			tan +:= MonomialCoefficient(f, m) * m;
// 		end if;
// 	end for;
// 	return tan;
// end function;


// function Blowup(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType)
// 	P := Parent(strictTransform_f); x := P.1; y := P.2; R := BaseRing(P);
// 	xExp_f, yExp_f := Explode(xyExp_f);
// 	xExp_w, yExp_w := Explode(xyExp_w);
	
// 	printf "----- Blowup -----\n\n";
	
// 	blownUpRupture := false;
// 	lambda := 0;
// 	PI_blowup := [x, y];
	
// 	while (not blownUpRupture) do
// 		tan := TangentTerm(strictTransform_f);
		
// 		if (Length(tan) eq 1) then
// 			if (Exponents(tan)[1] gt 0) then
// 				// Case tan = C * x^e
// 				pi := [x*y, x];
				
// 				PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
				
// 				// x^xExp * y^yExp -> (x*y)^xExp * x^yExp = x^(xExp+yExp) * y^xExp
// 				xExp_f, yExp_f := Explode(< xExp_f + yExp_f, xExp_f >);
// 				xExp_w, yExp_w := Explode(< xExp_w + yExp_w, xExp_w >);
				
// 				// Blow up each term, preserve multiplicity
// 				// They are units and will be units after blowups: no common x,y
// 				units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
// 				units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
				
// 				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
// 				xExp_f +:= A;
// 				yExp_f +:= B;
				
// 				// Pullback of dx^dy by pi
// 				// Ignoring multiplicative constant (-1) in w
// 				xExp_w +:= 1;
				
// 				if (pointType eq 0) then
// 					pointType := 1;
// 				else
// 					pointType := 2;
// 				end if;
				
// 			else
// 				// Case tan = C * y^e
// 				pi := [x, x*y];
				
// 				PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
				
// 				// x^xExp * y^yExp -> x^xExp * (x*y)^yExp = x^(xExp+yExp) * y^yExp
// 				xExp_f, yExp_f := Explode(< xExp_f + yExp_f, yExp_f >);
// 				xExp_w, yExp_w := Explode(< xExp_w + yExp_w, yExp_w >);
				
// 				// Blow up each term, preserve multiplicity
// 				// They are units and will be units after blowups: no common x,y
// 				units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
// 				units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
				
// 				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
// 				xExp_f +:= A;
// 				yExp_f +:= B;
				
// 				// Pullback of dx^dy by pi
// 				xExp_w +:= 1;
				
// 				if (pointType eq 2) then
// 					pointType := 2;
// 				else
// 					pointType := 1;
// 				end if;
				
// 			end if;
// 		else
// 			// Case tan = C * (x-lambda*y)^e, lambda =/= 0
			
// 			// Lambda
// 			e := Degree(tan, y);
// 			C := MonomialCoefficient(tan, x^e);
// 			// tan = C*x^e - C*e*lambda*x^(e-1)*y + ...
// 			lambda := MonomialCoefficient(tan, x^(e-1)*y) / (- C * e);
			
// 			pi := [x, x*y];
			
// 			PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
			
// 			// x^xExp * y^yExp -> x^xExp * (x*y)^yExp = x^(xExp+yExp) * y^yExp
// 			xExp_f, yExp_f := Explode(< xExp_f + yExp_f, yExp_f >);
// 			xExp_w, yExp_w := Explode(< xExp_w + yExp_w, yExp_w >);
			
// 			// Blow up each term, preserve multiplicity
// 			// They are units and will be units after blowups: no common x,y
// 			units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
// 			units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
			
// 			strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
// 			xExp_f +:= A;
// 			yExp_f +:= B;
			
// 			// Pullback of dx^dy by pi
// 			xExp_w +:= 1;
			
// 			if (pointType eq 2) then
// 				pointType := 1;
// 				blownUpRupture := true;
// 			else
// 				pointType := 1;
				
// 				printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// 				printf "strictTransform_f = %o\n", strictTransform_f;
// 				printf "xyExp_f = [ %o, %o ]\n", xExp_f, yExp_f;
// 				printf "xyExp_w = [ %o, %o ]\n", xExp_w, yExp_w;
// 				printf "units_f =\n";
// 				for t -> m in units_f do
// 					printf "    ( %o )^%o\n", t, m;
// 				end for;
// 				printf "units_w =\n";
// 				for t -> m in units_w do
// 					printf "    ( %o )^%o\n", t, m;
// 				end for;
// 				printf "\nlambda = %o\n", lambda;
				
// 				// Center intersecion with current exceptional divisor to (0,0)
				
// 				pi := [x, (1-y)/lambda];
				
// 				PI_blowup := [Evaluate(t, pi) : t in PI_blowup];
				
// 				// Change variables of each term, preserve multiplicity
// 				// They are units and will be units after change of variables
// 				// because the point is free: no common x,y
// 				units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
// 				units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
				
// 				// x^xExp * y^yExp -> x^xExp * ((1-y)/lambda)^yExp
// 				Include(~units_f, (pi[2])^^yExp_f);
// 				Include(~units_w, (pi[2])^^yExp_w);
// 				yExp_f := 0;
// 				yExp_w := 0;
				
// 				strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
// 				xExp_f +:= A;
// 				yExp_f +:= B;
				
// 				// Pullback of dx^dy by pi
// 				// Ignoring multiplicative constant (-1/lambda) in w
// 			end if;
// 		end if;
		
// 		printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// 		printf "strictTransform_f = %o\n", strictTransform_f;
// 		printf "xyExp_f = [ %o, %o ]\n", xExp_f, yExp_f;
// 		printf "xyExp_w = [ %o, %o ]\n", xExp_w, yExp_w;
// 		printf "units_f =\n";
// 		for t -> m in units_f do
// 			printf "    ( %o )^%o\n", t, m;
// 		end for;
// 		printf "units_w =\n";
// 		for t -> m in units_w do
// 			printf "    ( %o )^%o\n", t, m;
// 		end for;
// 		// printf "pointType = %o\n\n", pointType;
// 		printf "pointType = %o\n\n", pointType eq 0 select "start" else (pointType eq 1 select "free" else "satellite");
		
// 	end while;
	
// 	printf "PI_blowup = [ %o, %o ]\n\n", PI_blowup[1], PI_blowup[2];
	
// 	return strictTransform_f, [xExp_f,yExp_f], [xExp_w,yExp_w], units_f, units_w, pointType, lambda, PI_blowup;
// end function;


// function CenterOriginOnCurve(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, lambda)
// 	P := Parent(strictTransform_f); x := P.1; y := P.2; R := BaseRing(P);
// 	xExp_f, yExp_f := Explode(xyExp_f);
// 	xExp_w, yExp_w := Explode(xyExp_w);
	
// 	printf "----- CenterOriginOnCurve -----\n\n";
	
// 	// Center intersecion with current exceptional divisor to (0,0)
	
// 	pi := [x, (1-y)/lambda];
	
// 	// Change variables of each term, preserve multiplicity
// 	// They are units and will be units after change of variables
// 	// because the point is free: no common x,y
// 	units_f := {* Evaluate(t, pi)^^m : t -> m in units_f *};
// 	units_w := {* Evaluate(t, pi)^^m : t -> m in units_w *};
	
// 	// x^xExp * y^yExp -> x^xExp * ((1-y)/lambda)^yExp
// 	Include(~units_f, (pi[2])^^yExp_f);
// 	Include(~units_w, (pi[2])^^yExp_w);
// 	yExp_f := 0;
// 	yExp_w := 0;
	
// 	strictTransform_f, A, B := strictPart(Evaluate(strictTransform_f, pi));
// 	xExp_f +:= A;
// 	yExp_f +:= B;
	
// 	// Pullback of dx^dy by pi
// 	// Ignoring multiplicative constant (-1/lambda) in w
	
// 	printf "lambda = %o\n", lambda;
// 	printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// 	printf "strictTransform_f = %o\n", strictTransform_f;
// 	printf "xyExp_f = [ %o, %o ]\n", xExp_f, yExp_f;
// 	printf "xyExp_w = [ %o, %o ]\n", xExp_w, yExp_w;
// 	printf "units_f =\n";
// 	for t -> m in units_f do
// 		printf "    ( %o )^%o\n", t, m;
// 	end for;
// 	printf "units_w =\n";
// 	for t -> m in units_w do
// 		printf "    ( %o )^%o\n", t, m;
// 	end for;
// 	printf "\n";
	
// 	return strictTransform_f, [xExp_f,yExp_f], [xExp_w,yExp_w], units_f, units_w, pi;
// end function;



// f := -x^9 + 11*x^5*y^2 + y^4;
// (y^2-x^3)^2 + x^5*y;

// P, E := ProximityMatrix(f);
// printf "f = %o\n", f;
// printf "P = \n%o\n", P;
// printf "E = %o\n", E;

// -----------------------------------

// f := (y^2 - x^3)^2 + x^5*y;
// w := P!1;

// for i in [1..3] do
// 	pi, f, w := Blowup(f, w);
// 	printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// 	// printf "f = %o\n", f;
// 	printf "strict f = %o\n", strictPart(f);
// 	printf "w = %o\n", w;
// 	printf "\n";
// end for;

// lambda := 1;

// pi := [x, (1-y)/lambda];
// f := Evaluate(f, pi);
// w := Evaluate(w, pi) * (-1/lambda);
// printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// // printf "f = %o\n", f;
// printf "strict f = %o\n", strictPart(f);
// printf "w = %o\n", w;
// printf "\n";

// // Factorization(f);

// for i in [1..2] do
// 	pi, f, w := Blowup(f, w);
// 	printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// 	// printf "f = %o\n", f;
// 	printf "strict f = %o\n", strictPart(f);
// 	printf "w = %o\n", w;
// 	printf "\n";
// end for;


// lambda := -1;

// pi := [x, (1-y)/lambda];
// f := Evaluate(f, pi);
// w := Evaluate(w, pi) * (-1/lambda);
// printf "pi = [ %o, %o ]\n", pi[1], pi[2];
// // printf "f = %o\n", f;
// // printf "strict f = %o\n", strictPart(f);
// a, b := Factorization(f);
// printf "f = %o\n", b;
// for t in a do
// 	printf "    ( %o )^%o\n", t[1], t[2];
// end for;
// printf "w = %o\n", w;
// printf "\n";

// -------------------------------------

// printf "strictTransform_f = %o\n", strictTransform_f;
// printf "xyExp_f = [ %o, %o ]\n", xyExp_f[1], xyExp_f[2];
// printf "xyExp_w = [ %o, %o ]\n", xyExp_w[1], xyExp_w[2];
// printf "units_f =\n";
// for t -> m in units_f do
// 	printf "    ( %o )^%o\n", t, m;
// end for;
// printf "units_w =\n";
// for t -> m in units_w do
// 	printf "    ( %o )^%o\n", t, m;
// end for;
// printf "pointType = %o\n\n", pointType;

// -------------------------------------

// f := (y^2-x^3)^2 + x^5*y;
// f := (y-2*x-3*x^2)^4 - x^9;
// f := y^4 - x^9 + 17*x^5*y^2;
f := (x^3-y^7)^2 + x*y^12 + 17*x^2*y^10;

printf "f = %o\n\n", f;

strictTransform_f := f;
xyExp_f := [0,0];
xyExp_w := [0,0];
units_f := {* P!1 *};
units_w := {* P!1 *};
pointType := 0;
PI_TOTAL := [x, y];

strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType, LAMBDA, PI_blowup := Blowup(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType);

PI_TOTAL := [Evaluate(t, PI_blowup) : t in PI_TOTAL];
U := &*[t^m : t->m in units_f] * strictTransform_f;
V := &*[t^m : t->m in units_w];
printf "PI_TOTAL = [ %o, %o ]\n", PI_TOTAL[1], PI_TOTAL[2];
printf "U = %o\n", U;
printf "V = %o\n\n", V;


strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, PI_center := CenterOriginOnCurve(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, LAMBDA);

PI_TOTAL := [Evaluate(t, PI_center) : t in PI_TOTAL];
printf "PI_TOTAL = [ %o, %o ]\n\n", PI_TOTAL[1], PI_TOTAL[2];



strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType, LAMBDA, PI_blowup := Blowup(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, pointType);

PI_TOTAL := [Evaluate(t, PI_blowup) : t in PI_TOTAL];
U := &*[t^m : t->m in units_f] * strictTransform_f;
V := &*[t^m : t->m in units_w];
printf "PI_TOTAL = [ %o, %o ]\n\n", PI_TOTAL[1], PI_TOTAL[2];
printf "U = %o\n", U;
printf "V = %o\n\n", V;



strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, PI_center := CenterOriginOnCurve(strictTransform_f, xyExp_f, xyExp_w, units_f, units_w, LAMBDA);

PI_TOTAL := [Evaluate(t, PI_center) : t in PI_TOTAL];
printf "PI_TOTAL = [ %o, %o ]\n\n", PI_TOTAL[1], PI_TOTAL[2];



