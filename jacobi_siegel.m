declare type ModFrmJacobiTB;
declare attributes ModFrmJacobiTB: coeffs, weight, level, tb_d, tb_n, expansion, expansion_deg, coeffring, zetad;

intrinsic Print(phi::ModFrmJacobiTB) 
  {Print phi}
  
  printf "Jacobi form of weight %o and level %o arising from theta block TB_%o(%o)", 
    phi`weight, phi`level, phi`tb_n, phi`tb_d;
end intrinsic;

intrinsic ThetaBlock(n::RngIntElt, d::[RngIntElt] : CoefficientRing := Integers()) -> ModFrmJacobiTB
  {Define theta block}
  assert n eq 2;
  assert #d eq 10;
  
  phi := New(ModFrmJacobiTB);
  phi`tb_n := 2;
  phi`tb_d := d;
  N := &+[s^2 : s in d];
  assert N mod 2 eq 0;
  phi`weight := 2;
  phi`level := N div 2;
  phi`coeffring := CoefficientRing;
  return phi;
end intrinsic;

intrinsic Level(phi::ModFrmJacobiTB) -> RngIntElt
  {Level of phi}
  
  return phi`level;
end intrinsic;

intrinsic Weight(phi::ModFrmJacobiTB) -> RngIntElt
  {Weight of phi}
  
  return phi`weight;
end intrinsic;

intrinsic ThetaBlockData(phi::ModFrmJacobiTB) -> SeqEnum[RngIntElt]
  {Return theta block data}
  
  return phi`tb_d, phi`tb_n;
end intrinsic;

intrinsic CoefficientRing(phi::ModFrmJacobiTB) -> Rng
  {Return the coefficient ring}
  
  return phi`coeffring;
end intrinsic;

intrinsic Expansion(phi::ModFrmJacobiTB, prec::RngIntElt) -> RngSerPuisElt
  {Returns expansion of phi to precision prec, without extra zetas!}

  prec := Max(prec,2);

  if assigned phi`expansion and assigned phi`expansion_deg and phi`expansion_deg ge prec then
    return phi`expansion;
  end if;

  coeffring := phi`coeffring;
  _<zeta> := LaurentSeriesRing(FieldOfFractions(coeffring));
  _<q> := PowerSeriesRing(Parent(zeta));
  
  prec0 := Floor((1+Sqrt(1+8*prec))/2);
  function TB(d)
    return &+[ (-1)^(n+1)*q^(Binomial(n,2))*&+[ zeta^(d*j) : j in [-(n-1)..(n-1)]] : n in [1..prec0]] + O(q^prec);
  end function;
  
  d, n_theta := ThetaBlockData(phi);

  printf "  Computing Jacobi expansion for %o to prec %o...", d, prec;

  assert n_theta eq 2;
  if n_theta eq 2 then
    F := q * (&*[ 1-q^n+O(q^prec) : n in [1..prec-1]])^-6 * &*[ TB(di) : di in ThetaBlockData(phi)];
  end if;

  phi`zetad := zeta^(&+d div 2) * &*[ (1-zeta^(-di)) : di in ThetaBlockData(phi)];  
  phi`expansion := F;
  phi`expansion_deg := prec;
  
  printf "  done!\n";

  return F;
end intrinsic;

intrinsic Coefficient(phi::ModFrmJacobiTB, n::RngIntElt, r::RngIntElt) -> RngElt
  {c(n,r)*q^n*zeta^r coefficient of phi}

  _ := Expansion(phi, n+1);
  cn := Coefficient(phi`expansion,n);  
  return Coefficient(cn*phi`zetad,r);
end intrinsic;





declare type ModFrmSiegel;
declare attributes ModFrmSiegel: jacobi, level, weight, heckespecs, fouriercoeffs;

intrinsic Print(F::ModFrmSiegel)
  {Print F}
  
  printf "Siegel modular form of weight %o and level %o, a Gritsenko lift of %o",
    F`weight, F`level, F`jacobi;
end intrinsic;

intrinsic GritsenkoLift(phi::ModFrmJacobiTB) -> ModFrmSiegel
  {Gritsenko lift}
  
  F := New(ModFrmSiegel);
  F`jacobi := phi;
  F`weight := Weight(phi);
  F`level := Level(phi);
  F`fouriercoeffs := AssociativeArray();
  return F;
end intrinsic;

intrinsic Level(F::ModFrmSiegel) -> RngIntElt
  {Level of phi}
  
  return F`level;
end intrinsic;

intrinsic Weight(F::ModFrmSiegel) -> RngIntElt
  {Weight of phi}
  
  return F`weight;
end intrinsic;

intrinsic JacobiUnlift(F::ModFrmSiegel) -> ModFrmJacobiTB
  {Underlying Jacobi form}
  
  return F`jacobi;
end intrinsic;

intrinsic CoefficientRing(F::ModFrmSiegel) -> Rng
  {Return the coefficient ring}
  
  return CoefficientRing(JacobiUnlift(F));
end intrinsic;


intrinsic FourierCoefficient(F::ModFrmSiegel, T::AlgMatElt : Justn := false) -> RngElt
  {Fourier coefficient a_T(F)}
  
  if not Justn then
    bl, a := IsDefined(F`fouriercoeffs, T);
    if bl then return a; end if;
  end if;
  
  // printf "Computing Fourier coefficient a(T,F), where T = %o and F = %o:\n", Eltseq(T), F;

  k := F`weight;
  N := F`level;
  phi := F`jacobi;
  
  n := Integers()!T[1,1];
  r := Integers()!(2*T[1,2]);
  mN := Integers()!T[2,2];
  // assert mN mod N eq 0;
  m := mN div N;
    
  a := 0;
  for delta in Divisors(Gcd([n,r,m])) do
    t := Round(r/(2*delta*N)); // reduce coefficient
    r_red := Integers()!(r/delta - 2*t*N);
    mn_red := Integers()!(m*n/delta^2-t*r/delta+t^2*N);
//    bl, r_red := IsCoercible(Integers(), r_red);
//    assert bl;
//    bl, mn_red := IsCoercible(Integers(), m*n/delta^2-t*r/delta+t^2*N);
//    assert bl;
/*
    assert mn_red ge 0;
    assert 4*mn_red*N-r_red^2 eq (4*m*n*N-r^2)/delta^2;
    assert Coefficient(phi, mn_red, r_red) eq Coefficient(phi, (m*n) div delta^2, r div delta);
*/
    a +:= delta^(k-1)*Coefficient(phi, mn_red, r_red);
  end for;

  // printf " done!\n";

  F`fouriercoeffs[T] := a;
  if Justn then 
    return mn_red; 
  else 
    return a; 
  end if;
end intrinsic;

function SpecializationCoefficients(s0, N, nd);

  // printf "Computing specialization coefficients for s0 = %o and nd = %o...\n", Eltseq(s0), nd;

  a := s0[1,1];
  b := 2*s0[1,2];
  c := s0[2,2];
  g, n00,r00 := Xgcd(a,b div 2);
  ag := a div g;
  b2g := b div (2*g);
  
  outTs := [];

  D := a*c-b^2/4;
  // printf "  About to loop for m = 1 to %o with g = %o...\n", Floor(a*nd/(N*D)), g;
  for m := 1 to Floor(a*nd/(N*D)) do
    mN := m*N;
    y := nd-c*mN;
    if y mod g ne 0 then continue; end if;
    ydivg := y div g;
    n0 := n00*ydivg;
    r0 := r00*ydivg;
    eps := Floor(n0/b2g);
    n := n0 - b2g*eps;
    r := r0 + ag*eps;
    if n eq 0 then
      n +:= b2g;
      r -:= ag;
    end if;
    // assert n gt 0;
    while n lt Floor(c*nd/D) do
      if r^2 lt 4*n*mN then
        // assert a*n+1/2*b*r+c*m*N eq nd;
        Append(~outTs, Matrix([[n,r/2],[r/2,mN]]));
      end if;
      n +:= b2g;
      r -:= ag;
    end while;
  end for;

  // printf "  done!\n";

  return outTs;
end function;

intrinsic HeckeSpecialization(Fs::[ModFrmSiegel], s0::AlgMatElt, p::RngIntElt, prec::RngIntElt, Fnum, Fden 
                    : Operator := "T(p)") -> RngSerPowElt
  {Specialization of T_p(Fnum/Fden) at s0; choices for Operator are "T(p)" and "T_1(p^2)"}

  Fmo := Fs[1];
  
  N := Level(Fmo);
  k := Weight(Fmo);

  R := CoefficientRing(Fmo);
  FracR := FieldOfFractions(R);
  assert Operator in ["T(p)","T_1(p^2)"];
  if Operator eq "T(p)" then
    zeta_roots := Roots(CyclotomicPolynomial(p),FracR);
    if #zeta_roots gt 0 then
      zeta := zeta_roots[1][1];
      FracRzeta := FracR;
    else
      FracRzeta<zeta> := ext<FracR | Factorization(CyclotomicPolynomial(p),FracR)[1][1]>;
    end if;
  elif Operator eq "T_1(p^2)" then
    zeta_roots := Roots(CyclotomicPolynomial(p^2),FracR);
    if #zeta_roots gt 0 then
      zeta := zeta_roots[1][1];
      FracRzeta := FracR;
    else
      FracRzeta<zeta> := ext<FracR | Factorization(CyclotomicPolynomial(p^2),FracR)[1][1]>;
    end if;
  end if;
  _<q> := PuiseuxSeriesRing(FracRzeta);
  
  // four types of cosets
  if p eq 1 then
    ADBs := [[* Matrix([[1,0],[0,1]]),Matrix([[1,0],[0,1]]), [Matrix([[0,0],[0,0]])] *]];
  elif Operator eq "T(p)" then
    ADBs :=
    [[* Matrix([[p,0],[0,p]]),Matrix([[1,0],[0,1]]), [Matrix([[0,0],[0,0]])] *]]
    cat
    [[* Matrix([[1,0],[0,p]]),Matrix([[p,0],[0,1]]), [Matrix([[a,0],[0,0]]) : a in [0..p-1]] *]]
    cat
    [[* Matrix([[p,0],[a,1]]),Matrix([[1,-a],[0,p]]), [Matrix([[0,0],[0,b]]) : b in [0..p-1]] *] : a in [0..p-1]]
    cat   
    [[* Matrix([[1,0],[0,1]]),Matrix([[p,0],[0,p]]), [Matrix([[a,b],[b,c]]) : a,b,c in [0..p-1]] *]];
  elif Operator eq "T_1(p^2)" then
    ADBs := 
    [[* Matrix([[p,0],[0,p^2]]),Matrix([[p,0],[0,1]]), [Matrix([[0,0],[0,0]])] *]]
    cat
    [[* Matrix([[p^2,0],[p*a,p]]),Matrix([[1,-a],[0,p]]), [Matrix([[0,0],[0,0]])] *] : a in [0..p-1]]
    cat
    [[* Matrix([[p,0],[0,p]]),Matrix([[p,0],[0,p]]), [Matrix([[b,0],[0,0]]) : b in [1..p-1]] *]]
    cat
    [[* Matrix([[p,0],[0,p]]),Matrix([[p,0],[0,p]]), [Matrix([[a*b^2,a*b],[a*b,a]]) : a in [1..p-1], b in [0..p-1]] *]]
    cat
    [[* Matrix([[1,0],[0,p]]),Matrix([[p^2,0],[0,p]]), [Matrix([[d,c],[p*c,0]]) : d in [0..p^2-1], c in [0..p-1]] *]]
    cat    
    [[* Matrix([[p,0],[a,1]]),Matrix([[p,-p*a],[0,p^2]]), [Matrix([[0,p*b],[b,c]]) : b in [0..p-1], c in [0..p^2-1]] *] : a in [0..p-1]];
  end if;

  ADBcnt := 0;

  Fmo`heckespecs := AssociativeArray();

  printf "Precomputing Jacobi expansions...\n";
  for F in Fs do
    _ := Expansion(JacobiUnlift(F), 10*p);
  end for;

  TpFsum := O(q^prec);
  for ADBvec in ADBs do
    ADBTns := [];
    nmaxs := [];
    pdens := [];

    A := ADBvec[1];
    D := ADBvec[2];
    Bs := ADBvec[3];
    hecketot := #Bs;
    printf "Entering Hecke type A = %o, D = %o, totalling %o...\n", Eltseq(A), Eltseq(D), hecketot;
    print TpFsum;
    Dinv := ChangeRing(D,Rationals())^-1;
    if Operator eq "T(p)" then
      Dinvp := ChangeRing(p*Dinv,Integers());
    else
      Dinvp2 := ChangeRing(p^2*Dinv,Integers());
    end if;
    _, ADsqrt := IsSquare(Determinant(A*D));
    mu := (Determinant(D))^(-k)*(ADsqrt)^(2*k-3);
    As0Dinv := A*s0*Dinv;
    pden := Denominator(As0Dinv);
    qopden := q^(1/pden);
    As0Dadj := ChangeRing(As0Dinv*pden, Integers());

    printf "Computing specialization coefficients, totalling %o...\n", hecketot;
    Tns := [];
    for n := 1 to prec*pden-1 do
      bl, T0 := IsDefined(Fmo`heckespecs, <As0Dadj, N, n>);
      if not bl then
        T0 := SpecializationCoefficients(As0Dadj, N, n);
        (Fmo`heckespecs)[<As0Dadj,N,n>] := T0;
      end if;
      Append(~Tns,T0);
    end for;

    printf "Computing needed Fourier coefficients...\n";
    for F in Fs do
      for n := 1 to prec*pden-1 do
        _ := [FourierCoefficient(F, T) : T in Tns[n]];
      end for;
    end for;

    printf "Doing Hecke sum...\n";
    cputime := Cputime();
    Bcnt := 0;
    for B in Bs do
      Bcnt +:= 1;
      if Bcnt mod 100 eq 0 then
        printf "  done %o of %o, time/operator %os, time remaining %os...\n", Bcnt, hecketot, RealField(4)!(Cputime()-cputime)/Bcnt, RealField(4)!(Cputime()-cputime)*(hecketot-Bcnt)/Bcnt;
        print TpFsum;
      end if;
        
      s0TpFs := [];

      if Operator eq "T(p)" then
        BDinvp := B*Dinvp;
        BDinvpTs := [[zeta^(Integers()!Trace(BDinvp*T)) : T in Tns[n]] : n in [1..#Tns]];
        for F in Fs do
          s0TpF := [0] cat [&+([0] cat [(F`fouriercoeffs)[Tns[n][j]]*BDinvpTs[n][j] : j in [1..#Tns[n]]]) : n in [1..prec*pden-1]];
          s0TpF := mu*Evaluate(Parent(q)!s0TpF, qopden) + O(q^prec);
          Append(~s0TpFs, s0TpF);
        end for;
      elif Operator eq "T_1(p^2)" then
        BDinvp2 := B*Dinvp2;
        BDinvp2Ts := [[zeta^(Integers()!Trace(BDinvp2*T)) : T in Tns[n]] : n in [1..#Tns]];
        for F in Fs do
          s0TpF := [0] cat [&+([0] cat [(F`fouriercoeffs)[Tns[n][j]]*BDinvp2Ts[n][j] : j in [1..#Tns[n]]]) : n in [1..prec*pden-1]];
          s0TpF := mu*Evaluate(Parent(q)!s0TpF, qopden) + O(q^prec);
          Append(~s0TpFs, s0TpF);
        end for;
      end if;
      
      Tpjnum := Evaluate(Fnum,s0TpFs);
      Tpjden := Evaluate(Fden,s0TpFs);
      if IsWeaklyZero(Tpjnum) and IsWeaklyZero(Tpjden) then 
        qnd := O(q^(AbsolutePrecision(Tpjnum)-AbsolutePrecision(Tpjden)));
      else
        qnd := Tpjnum/Tpjden;
      end if;
      TpFsum +:= qnd;
    end for;
  end for;
  
  return TpFsum;  
end intrinsic; 