import "SemiGroup.m": Euclides, TailExponentSeries;

PuiseuxInfo := function(s)
  if Type(s) eq RngMPolLocElt then return [<[<0,0>], [0, Infinity()]>]; end if;
  E := CharExponents(s); T := TailExponentSeries(s);
  I := []; E cat:= [T]; n := E[1][2];
  // For each characteristic exponent...
  for i in [2..#E] do
    mj := E[i - 1][1]; nj := E[i - 1][2]; mi := E[i][1]; ni := E[i][2];
    h0 := (mi - mj) div nj; sat := Euclides(mi - mj, nj)[1];
    free := [<e, Coefficient(s, e)> : e in [(mj + k*nj)/n : k in [0..h0]]];
    Append(~I, <free, sat>);
  end for; return I;
end function;

ContactNumberExp := function(expInfoA, expInfoB)
  ContactNum := 0;
  // Free points associated with the char. exponent.
  freeA := expInfoA[1]; freeB := expInfoB[1];
  // Satellite points associated with the char. exponent.
  satA := expInfoA[2]; satB := expInfoB[2];
  // Compare free points.
  for i in [1..Min(#freeA, #freeB)] do
    if freeA[i] eq freeB[i] then ContactNum := ContactNum + 1;
    else return ContactNum, false; end if;
  end for;
  // If the num. of free points is not the same, no more points can be shared.
  if #freeA ne #freeB then return ContactNum, false; end if;
  // Compare satellite points.
  satA[#satA] := satA[#satA] - 1; satB[#satB] := satB[#satB] - 1;
  for i in [2..Min(#satA, #satB)] do
    ContactNum := ContactNum + Min(satA[i], satB[i]);
    if satA[i] ne satB[i] then return ContactNum, false; end if;
  end for;
  // If the number of stairs is not the same, no more points can be shared.
  if #satA ne #satB then return ContactNum, false; end if;
  // Otherwise, all the points are shared.
  return ContactNum, true;
end function;

ContactNumber := function(branchInfoA, branchInfoB)
  ContactNum := 0;
  // For each characteristic exponent...
  for r in [1..Min(#branchInfoA,#branchInfoB)] do
    // Get the contact num. of this char. exponent and wheter
    // or not we should compare more points.
    C, cont := ContactNumberExp(branchInfoA[r], branchInfoB[r]);
    ContactNum := ContactNum + C;
    if not cont then break; end if;
  end for; return ContactNum;
end function;

ContactMatrix := function(branches)
  //Add a dummy term so compare exact branches is easier.
  max := Max([0] cat [s[1] eq 0 select 0 else
    Ceiling(Degree(s[1])) : s in branches]) + 1;
  branches := [* <s[1] + (Parent(s[1]).1)^max, s[2]> : s in branches *];
  info := [PuiseuxInfo(s[1]) : s in branches];
  contact := ScalarMatrix(#branches, 1);
  // For each pair of branches compute their contact number.
  for i in [1..#branches] do
    for j in [i+1..#branches] do
      contactNum := ContactNumber(info[i], info[j]);
      contact[i][j] := contactNum; contact[j][i] := contactNum;
    end for;
  end for; return contact;
end function;

ProximityMatrixSemiGroup := function(H, maxContact : ExtraPoint := false)
  // Smooth inverted branches could have 2 char exps.
  if #H eq 2 and #H[1] eq 2 and H[1][1] eq 0 then Prune(~H); end if;
  // Dimension of the proximity matrix.
  N := Max(&+[IntegerRing() | &+h : h in Prune(H)], maxContact);
  if ExtraPoint then N := N + 1; end if;
  // Construct a proximity matrix with free points only.
  P := ScalarMatrix(N, 1);
  for i in [2..N] do P[i][i - 1] := -1; end for;
  // Fill in satellite points proximities.
  for i in [1..#H] do
    // Inverted axis case.
    if i eq 1 and H[1][1] eq 0 then j0 := 3; else j0 := 2; end if;
    Hi := H[i]; Hi[#Hi] := Hi[#Hi] - 1;
    for j in [j0..#Hi] do
      l := &+[IntegerRing() | &+H[k] : k in [1..i - 1]] + &+Hi[1..j - 1];
      for k in [1..Hi[j]] do P[l + k + 1, l] := -1; end for;
    end for;
  end for; return P;
end function;

ProximityMatrixBranch := function(s, maxContact : ExtraPoint := false)
  // If the branch is the y-axis.
  if Type(s) eq RngMPolLocElt then
    if ExtraPoint then maxContact := maxContact + 1; end if;
    // Construct a proximity matrix with free points only.
    P := ScalarMatrix(maxContact, 1);
    for i in [2..maxContact] do P[i][i - 1] := -1; end for;
    return P;
  end if; // Otherwise, the branch is represented by a Puiseux series.
  H := [charExps[2] : charExps in PuiseuxInfo(s)];
  return ProximityMatrixSemiGroup(H, maxContact : ExtraPoint := ExtraPoint);
end function;

MultiplicityVectorBranch := function(s, maxContact: ExtraPoint := false)
  // If the branch is the y-axis.
  if Type(s) eq RngMPolLocElt then
    if ExtraPoint then maxContact := maxContact + 1; end if;
    return Vector([1 : i in [1..maxContact]]);
  end if; // Otherwise, the branch is represented by a Puiseux series.
  M := []; E := CharExponents(s);
  for i in [2..#E] do
    mj := E[i-1][1]; nj := E[i-1][2]; mi := E[i][1]; ni := E[i][2];
    Hs := Euclides(mi - mj, nj)[1]; Ns := Euclides(mi - mj, nj)[2];
    for j in [1..#Hs] do M cat:= [Ns[j] : k in [1..Hs[j]]]; end for;
  end for;
  M cat:= [1 : i in [1..(maxContact - #M)]];
  if ExtraPoint then M cat:= [1]; end if;
  return Vector(M);
end function;

CoefficientsVectorBranch := function(s, maxContact)
  // If the branch is the y-axis
  R := CoefficientRing(Parent(s));
  if Type(s) eq RngMPolLocElt then
    return [<1, R!0>] cat [<0, R!1> : i in [1..maxContact]];
  end if; // Otherwise, the branch is represented by a Puiseux series.
  I := PuiseuxInfo(s); C := [];
  for i in [1..#Prune(I)] do
    C cat:= [<1, freePoint[2]> : freePoint in I[i][1]];
    Hi := I[i][2]; Hi[#Hi] := Hi[#Hi] - 1;
    C cat:= [<0, R!1> : j in [1..&+Hi[2..#Hi]]];
  end for;
  C cat:= [<1, freePoint[2]> : freePoint in I[#I][1]];
  if #C lt maxContact then
    C cat:= [<1, R!0> : i in [1..(maxContact - #C)]];
  end if;
  // The 0 Puiseux series must be treated separately.
  if s eq 0 then C cat:= [<1, R!0>]; end if;
  return C;
end function;

function ProximityMatrixImpl2(contactMat, branchesProx)
  if #branchesProx eq 0 then return <ScalarMatrix(0, 0), []>; end if;
  /////////////////////////// Base case ////////////////////////////////
  // If there is only branch, return its prox. matrix.
  if #branchesProx eq 1 then
    return <branchesProx[1], [[i : i in [1..Ncols(branchesProx[1])]]]>;
  end if;
  ////////////////////// Compute the splits /////////////////////////////
  // Substract one to all the contact numbers except the diagonal ones.
  N := Nrows(contactMat); ZZ := IntegerRing();
  contactMat := contactMat - Matrix(N, [ZZ | 1: i in [1..N^2]])
    + ScalarMatrix(N, 1);
  // Identify each current branch with an ID from 1 to #branches.
  C := contactMat; remainingBranches := [i : i in [1..N]]; S := [];
  // Splits will contain lists of branches ID, where two branches will
  // be in the same list iff they do not separate in the current point.
  while #remainingBranches ne 0 do
    // Get the contact number of the first remaining branch.
    branchCont := ElementToSequence(C[1]);
    // Get the positions of the branches with contact > 1 & contact = 1.
    sameBranchIdx := [i : i in [1..#branchCont] | branchCont[i] ne 0];
    otherBranchIdx := [i : i in [1..#branchCont] | branchCont[i] eq 0];
    // Save the branches with contact > 1 together and remove them since they
    // have been splitted from the rest of branches.
    Append(~S, remainingBranches[sameBranchIdx]);
    remainingBranches := remainingBranches[otherBranchIdx];
    // Compute the contact matrix of the remaining brances.
    C := Submatrix(C, otherBranchIdx, otherBranchIdx);
  end while;
  ///////////// Compute the prox. matrix of each subdiagram /////////////
  // Substract one to all the contact numbers and erase the
  // first point of the proximity matricies of the current
  // branches since we are moving down the Enriques diagram.
  newBranchProx := [*RemoveRowColumn(branchP, 1, 1) : branchP in branchesProx*];
  // Traverse each sub-diagram recursivaly.
  splitResult := [* ProximityMatrixImpl2(Submatrix(contactMat, split, split),
    newBranchProx[split]) : split in S *];
  ///////////////// Merge the prox. matrix of each split ////////////////
  // Create the matrix that will hold the proximity branch of this subdiagram.
  numPoints := &+[ZZ | Ncols(X[1]) : X in splitResult] + 1;
  P := ScalarMatrix(numPoints, 1); rowPoint := []; k := 1;
  // For each set of branches that splits in this node...
  for s in [1..#S] do
    // Get the proximity matrix & the position of the points
    // (relative to that prox. matrix) of the s-th subdiagram.
    X := splitResult[s]; M := X[1]; splitRowPoint := X[2];
    // Copy the submatrix M inside P with the top left entry in (k+1, k+1)
    InsertBlock(~P, M, k + 1, k + 1);
    // Sum k+1 and add the new point ({0}) to the position of the
    // points relative to the prox. matrix of the subdiagram.
    splitRowPoint := [[1] cat [p + k : p in pp] : pp in splitRowPoint];
    rowPoint cat:= splitRowPoint;
    // Use the information in splitRowPoint to set the proximities of
    // the current point into the new prox. matrix (P):
    // For each branch in this subdiagram...
    for i in [1..#S[s]] do
      Q := branchesProx[S[s][i]];
      // For each element int the first column...
      for j in [1..Ncols(Q)] do P[splitRowPoint[i][j]][1] := Q[j][1]; end for;
    end for;
    k := k + Ncols(M);
  end for;
  // Make sure rowPoint is returned in the original order.
  SS := []; for split in S do SS cat:= split; end for;
  SS := [Position(SS, i) : i in [1..#SS]];
  return <P, rowPoint[SS]>;
end function;

function ProximityMatrixImpl(branches: ExtraPoint := false)
  // Compute the proximity matrix, the contact matrix, the mult.
  // vector of each branch and its coefficients.
  contactMat := ContactMatrix(branches);
  branchProx := [* ProximityMatrixBranch(branches[i][1],
    Max(ElementToSequence(contactMat[i])) :
    ExtraPoint := ExtraPoint) : i in [1..#branches] *];
  branchMult := [* branches[i][2] * MultiplicityVectorBranch(branches[i][1],
    Max(ElementToSequence(contactMat[i])) :
    ExtraPoint := ExtraPoint) : i in [1..#branches] *];
  branchCoeff := [ CoefficientsVectorBranch(branches[i][1],
    Max(ElementToSequence(contactMat[i])) + 1) : i in [1..#branches] ];
  // Get the proximity matrix of f and the position of each infinitely
  // near point inside the prox. matrix.
  X := ProximityMatrixImpl2(contactMat, branchProx);
  // Finally, rearrange each point's multiplicity so its position is coherent
  // coherent with the prox. matrix P.
  P := X[1]; R := X[2]; E := [RMatrixSpace(IntegerRing(), 1, Ncols(P)) | ];
  for i in [1..#branches] do
    Append(~E, ZeroMatrix(IntegerRing(), 1, Nrows(P)));
    for j in [1..#R[i]] do E[i][1, R[i][j]] := branchMult[i][j]; end for;
  end for; return P, E, branchCoeff;
end function;

intrinsic ProximityMatrix(f::RngMPolLocElt: ExtraPoint := false,
                          Coefficients := false, Branches := false) -> []
{ Computes the proximity matrix of the resolution of a plane curve }
  // Get the general Puiseux expansion of f.
  branches := PuiseuxExpansion(f);
  P, E, C := ProximityMatrixImpl(branches: ExtraPoint := ExtraPoint);
  if not Coefficients then
    if not Branches then return P, &+E; else return P, E; end if;
  end if;
  CC := [Parent(C[1][1]) | <1, 0> : i in [1..Nrows(P)]];
  for i in [1..#E] do
    I := [j : j in [1..Ncols(P)] | E[i][1][j] ne 0];
    for j in [1..#I] do CC[I[j]] := C[i][j]; end for;
  end for;
  if not Branches then return P, &+E, CC;
  else return P, E, CC; end if;
end intrinsic;

intrinsic ProximityMatrix(G::[RngIntElt] : ExtraPoint := false) -> []
{ Computes the proximity matrix of the resolution of a plane curve
  with semigroup G }

  ZZ := Integers(); N := Gcd(G); G := [ZZ!(g/N) : g in G];
  require IsPlaneCurveSemiGroup(G): "Argument must be a plane curve semigroup";
  C := CharExponents(G) cat []; n := C[1][2]; I := [];
  // For each characteristic exponent...
  for i in [2..#C] do
    mj := C[i - 1][1]; nj := C[i - 1][2]; mi := C[i][1]; ni := C[i][2];
    h0 := (mi - mj) div nj; sat := Euclides(mi - mj, nj)[1];
    Append(~I, sat);
  end for; I cat:= [[0]];
  P := ProximityMatrixSemiGroup(I, 1 : ExtraPoint := ExtraPoint);
  e := ZeroMatrix(ZZ, 1, Ncols(P)); e[1, Ncols(P)] := N;
  return P, e*P^-1;
end intrinsic;

intrinsic ContactMatrix(f::RngMPolLocElt) -> []
{ Computes de contact numbers of the branches of f }

  S := PuiseuxExpansion(f);
  P, E := ProximityMatrixImpl(S); N := Ncols(P);
  C := ScalarMatrix(#S, 0);
  for i in [1..#S] do for j in [i + 1..#S] do
      C[i][j] := &+[E[i][1][k] * E[j][1][k] : k in [1..N]];
  end for; end for;
  return C + Transpose(C);
end intrinsic;
