Attach("jacobi_siegel.m");

cputime := Cputime();


N := 277;
TBs := [
[2, 4, 4, 4, 5, 6, 8, 9, 10, 14],
[2, 3, 4, 5, 5, 7, 7, 9, 10, 14],
[2, 3, 4, 4, 5, 7, 8, 9, 11, 13],
[2, 3, 3, 5, 6, 6, 8, 9, 11, 13],
[2, 3, 3, 5, 5, 8, 8, 8, 11, 13],
[2, 3, 3, 5, 5, 7, 8, 10, 10, 13],
[2, 3, 3, 4, 5, 6, 7, 9, 10, 15],
[2, 2, 4, 5, 6, 7, 7, 9, 11, 13],
[2, 2, 4, 4, 6, 7, 8, 10, 11, 12],
[2, 2, 3, 5, 6, 7, 9, 9, 11, 12]
];

_<G1,G2,G3,G4,G5,G6,G7,G8,G9,G10> := PolynomialRing(Integers(),10);
Fnum := - 14*G1^2 - 20*G8*G2 + 11*G9*G2 + 6*G2^2 - 30*G7*G10 + 15*G9*G10
           + 15*G10*G1 - 30*G10*G2 - 30*G10*G3 + 5*G4*G5 + 6*G4*G6 + 17*G4*G7
           - 3*G4*G8 - 5*G4*G9 - 5*G5*G6 + 20*G5*G7 - 5*G5*G8 - 10*G5*G9 - 3*G6^2
           + 13*G6*G7 + 3*G6*G8 - 10*G6*G9 - 22*G7^2 + G7*G8 + 15*G7*G9 + 6*G8^2
           - 4*G8*G9 - 2*G9^2 + 20*G1*G2 - 28*G3*G2 + 23*G4*G2 + 7*G6*G2
           - 31*G7*G2 + 15*G5*G2 + 45*G1*G3 - 10*G1*G5 - 2*G1*G4 - 13*G1*G6
           - 7*G1*G8 + 39*G1*G7 - 16*G1*G9 - 34*G3^2 + 8*G3*G4 + 20*G3*G5
           + 22*G3*G6 + 10*G3*G8 + 21*G3*G9 - 56*G3*G7 - 3*G4^2;
Fden := - G4 + G6 + 2*G7 + G8 - G9 + 2*G3 - 3*G2 - G1;

s0 := Matrix([[554,233],[233,98]]);

/*
N := 353;
TBs := [
[3, 4, 4, 4, 6, 7, 8, 10, 12, 16],
[3, 3, 4, 4, 5, 7, 7, 10, 12, 17],
[2, 3, 5, 5, 6, 7, 9, 10, 11, 16],
[2, 3, 5, 5, 6, 7, 8, 10, 13, 15],
[2, 3, 5, 5, 5, 7, 10, 10, 12, 15],
[2, 3, 4, 6, 6, 7, 9, 9, 13, 15],
[2, 3, 4, 6, 6, 7, 8, 10, 14, 14],
[2, 3, 4, 5, 6, 7, 9, 11, 13, 14],
[2, 3, 4, 5, 5, 7, 8, 9, 12, 17],
[2, 3, 4, 4, 6, 8, 10, 11, 12, 14],
[2, 3, 3, 5, 6, 9, 9, 11, 12, 14]
];

_<G1,G2,G3,G4,G5,G6,G7,G8,G9,G10,G11> := PolynomialRing(Integers(),11);
Fnum := - G10*G11 - 2*G11*G2 + G10*G3 + 4*G11*G3 + 2*G2*G3 - 4*G3^2 - 5*G11*G4 
      + 5*G3*G4 + G11*G5 - G3*G5 + 6*G11*G6 - 6*G3*G6 - 11*G1*G7 + 11*G10*G7 
      - 9*G11*G7 + 9*G3*G7 + 11*G4*G7 - 11*G6*G7 + 11*G7^2 + 11*G1*G8 
      - 11*G10*G8 + 9*G11*G8 - 9*G3*G8 - 11*G4*G8 + 11*G6*G8 - 22*G7*G8 
      + 11*G8^2 - 2*G11*G9 + 2*G3*G9;
Fden := - G11 + G3;

s0 := Matrix([[706,84],[84,10]]);
// s0 := Matrix([[2118,92],[92,4]]);
*/

printf "Finding prime...";
p := 2;
ell := Ceiling(2*(1+p)*(1+p^2)/p);
ell +:= 1-ell mod p;
if ell mod 2 eq 0 then
  ell +:= p;
end if;
while not IsPrime(ell) do
  ell +:= p;
end while;
printf " done, taking ell = %o\n", ell;
      
phis := [ThetaBlock(2, TB : CoefficientRing := Integers()) : TB in TBs];
Fs := [GritsenkoLift(phi) : phi in phis];

TpfN := HeckeSpecialization(Fs,s0,p,40, Fnum, Fden);
fN := HeckeSpecialization(Fs,s0,1,40, Fnum, Fden);

ap := Integers()!Coefficient(TpfN/fN,0);
if ap gt ell/2 then ap -:= ell; end if;
print p, ap;
print Cputime() - cputime;



