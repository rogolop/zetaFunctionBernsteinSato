177,0
S,FormalDerivative,"Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to xi. 		 		F : sequence of sequences m times, where F[a1,...,am] represents the 							coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...). 		indexsF : nonzero elements of F. 		g : sequence of functions [g1,...,gm] of (x1,...). 		xi : derive with respect to xi",1,2,1,82,0,469,4,0,0,0,0,0,0,0,469,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivative,"Formal derivative of the composition (F o (g1,...,gm))(x1,...) with respect to xi. 		 		F : sequence of sequences m times, where F[a1,...,am] represents the 							coefficient of (d_1^(a1-1) ... d_m^(am-1))F at (g1,...,gm)(x1,...). 		indexsF : nonzero elements of F. 		g : sequence of functions [g1,...,gm] of (x1,...). 		i : derive with respect to the i-th variable",1,2,1,82,0,469,4,0,0,0,0,0,0,0,148,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivative,"Derivative of (F o g), k times with respect to xi",1,2,1,82,0,469,5,0,0,0,0,0,0,0,469,,0,0,148,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivative,"Derivative of (F o g), k times with respect to the i-th variable",1,2,1,82,0,469,5,0,0,0,0,0,0,0,148,,0,0,148,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivative,"L = Set( <k_1,i_1>, ..., <k_n,i_n> ) 			or 		L = Set( <k_1,x_i_1>, ..., <k_n,x_i_n> ). 		Derivate of (F o g) with respect to x_i, k times, for all <k,x_i> in L",2,2,1,82,0,469,3,1,82,0,303,4,0,0,0,0,0,0,0,82,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivativeDiscardingVar,"Derivative of (F o g), k times with respect to xi. 		Discard terms with powers higher than x_discardVar^discardPow at the result",1,2,1,82,0,469,6,0,0,0,0,0,0,0,82,,0,0,469,,0,0,148,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivativeDiscardingVar,"Derivative of (F o g), k times with respect to the i-th variable. 		Discard polynomials that will result in x_discardVar^discardPow*(...) at the result",1,2,1,82,0,469,6,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FormalDerivativeDiscardingVar,"L = Set( <k_1,i_1>, ..., <k_n,i_n> ) 			or 		L = Set( <k_1,x_i_1>, ..., <k_n,x_i_n> ). 		Derivate of (F o g) with respect to x_i, k times, for all <k,x_i> in L. 		Discard polynomials that will result in x_discardVar^discardPow*(...) at the result",2,2,1,82,0,469,3,1,82,0,303,5,0,0,0,0,0,0,0,82,,0,0,82,,0,0,82,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,E,"Gamma(l+epsilon+1) * Gamma(sigma-i+1) / Gamma(l+epsilon+sigma-i+2) * 1/ref, with ref = Gamma(a) * Gamma(b) / Gamma(c), where a,b,c are in the interval (0,1] differing of the first values by integer numbers",0,4,0,0,0,0,0,0,0,148,,0,0,82,,0,0,148,,0,0,148,,237,-38,-38,-38,-38,-38
S,SeparateYTerms,"Convert each polynomial in s to a sequence of pairs [l,term], there term is the coefficient of y^l of the polynomial (as member of R[y] with the corresponding ring R)",0,2,0,0,0,0,0,0,0,83,,0,0,82,,82,-38,-38,-38,-38,-38
S,nonconjugateResidue,"""Nonconjugate"" part of the residue of the complex zeta function, with indexing representing the derivatives of delta(x,y). Multiply the result by its conjugate to obtain the full residue (apart from the multiplying constant)",0,6,0,0,0,0,0,0,0,148,,0,0,82,,0,0,-25,,0,0,267,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,FactorizedBasis,"Get a simplified basis of polynomials, as sequences of factors without multiplicity, without denominators",0,4,0,0,0,0,0,0,0,82,,0,0,470,,0,0,83,,0,0,82,,82,-38,-38,-38,-38,-38
S,PrintStratification,print [[]] containing the polynomials where a residue is 0,1,0,1,82,0,82,4,0,0,1,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,82,,-38,-38,-38,-38,-38,-38
S,PrintStratificationAsCSV,print [[]] containing the polynomials where a residue is 0,1,0,1,82,0,82,4,0,0,1,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,82,,-38,-38,-38,-38,-38,-38
S,PrintStratificationAsLatex,print [[]] containing the polynomials where a residue is 0,1,0,1,82,0,82,4,0,0,1,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,82,,-38,-38,-38,-38,-38,-38
S,ZetaFunctionResidue,"Return and print stratification of the residue of the complez zeta function at candidate poles corresponding to nus in rupture divisor r, each one as [[]] which is a sequence of generators of the zero ideal, represented as sequences containing their irreducible factors",0,1,0,0,0,0,0,0,0,303,,168,168,168,-38,-38,-38
S,DiscardHigherPow,Discard terms with powers of var higher than var^pow,0,3,0,0,0,0,0,0,0,148,,0,0,-1,,0,0,-1,,-1,-38,-38,-38,-38,-38
S,Evaluate,Evaluate a multivariate rational function in x_i=r 		Necessary in construction of curve from _betas,0,3,0,0,0,0,0,0,0,-45,,0,0,148,,0,0,237,,237,-38,-38,-38,-38,-38
