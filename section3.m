

/*
202307200104
The code verifying the proofs of Section 3.
*/



///////////////////////////////////////////
//INPUT
///////////////////////////////////////////


P<x> := PolynomialRing(RationalField());

"For J := the Jacobian of X_1(11):";
E := EllipticCurve([0, -1, -1, 0, 0]);
E;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(E));
for p in [3,5] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

printf "rankJ(Q) <= %o \n", RankBound(E);

"---------------------------------------------";

"For J := the Jacobian of X_1(13):";
C := HyperellipticCurve(x^6 - 2 * x^5 + x^4 - 2 * x^3 + 6 * x^2 - 4 * x + 1);
J := Jacobian(C);
J;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(J));
for p in [3,5] do;
    Jp := BaseChange(J, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Jp));
end for;

printf "rankJ(Q) <= %o \n", RankBound(J);

"---------------------------------------------";

"For J := the Jacobian of X_1(14):";
E := EllipticCurve([1, 0, 1, -1, 0]);
E;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(E));
for p in [3,13] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

printf "rankJ(Q(sqrt-7)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,-7]];

"---------------------------------------------";

"For J := the Jacobian of X_1(15):";
E := EllipticCurve([1, 1, 1, 0, 0]);
E;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(E));
for p in [7,13] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

"The irreducible factors of \varphi_8/\varphi_4, where \varphi_n is the n-th division polynomial of J, are:";
for f in Factorization(DivisionPolynomial(E, 8) div DivisionPolynomial(E, 4)) do;
    if Exponent(GaloisGroup(f[1])) le 2 then;
        f[1];
    end if;
end for;

printf "rankJ(Q(sqrt-3, sqrt5)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,-3,5,-15]];

"---------------------------------------------";

"For J := the Jacobian of X_1(16):";
C := HyperellipticCurve(x * (x^2 + 1) * (x^2 + 2 * x - 1));
J := Jacobian(C);
J;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(J));
for p in [3,5] do;
    Jp := BaseChange(J, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Jp));
end for;

printf "rankJ(Q(sqrt-1, sqrt2)) <= %o \n", &+[RankBound(Jacobian(QuadraticTwist(C,d))) : d in [1,-1,2,-2]];

"---------------------------------------------";

"For J := the Jacobian of X_1(18):";
C := HyperellipticCurve(x^6 + 2 * x^5 + 5 * x^4 + 10 * x^3 + 10 * x^2 + 4 * x + 1);
J := Jacobian(C);
J;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(J));
for p in [7,11] do;
    Jp := BaseChange(J, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Jp));
end for;

printf "J^(3)(Q)_tors = %o \n", Invariants(TorsionSubgroup(Jacobian(QuadraticTwist(C,-3))));

printf "rankJ(Q(sqrt-3)) <= %o \n", &+[RankBound(Jacobian(QuadraticTwist(C,d))) : d in [1,-3]];

"---------------------------------------------";

"For J := the Jacobian of X_1(2,10):";
E := EllipticCurve("20a2");
E;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(E));
for p in [3,7] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

printf "rankJ(Q(sqrt5)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,5]];

"---------------------------------------------";

"For J := the Jacobian of X_1(2,12):";
E := EllipticCurve("24a4");
E;
printf "J(Q)_tors = %o \n", Invariants(TorsionSubgroup(E));
for p in [5,7] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

"The irreducible factors of \varphi_8/\varphi_4, where \varphi_n is the n-th division polynomial of J, are:";
for f in Factorization(DivisionPolynomial(E, 8) div DivisionPolynomial(E, 4)) do;
    if Exponent(GaloisGroup(f[1])) le 2 then;
        f[1];
    end if;
end for;

printf "rankJ(Q(sqrt-1, sqrt3)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,-1,3,-3]];

"---------------------------------------------";

"For J := the Jacobian of X_1(3,9):";
E := EllipticCurve("27a3");
BaseChange(EllipticCurve("27a3"), QuadraticField(-3));
printf "J(Q(sqrt(-3)))_tors = %o \n", Invariants(TorsionSubgroup(BaseChange(E, QuadraticField(-3))));
for p in [5,7] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

printf "rankJ(Q(sqrt-3)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,-3]];

"---------------------------------------------";

"For J := the Jacobian of X_1(4,8):";
E := EllipticCurve("32a2");
BaseChange(EllipticCurve("27a3"), QuadraticField(-1));
printf "J(Q(sqrt(-1)))_tors = %o \n", Invariants(TorsionSubgroup(BaseChange(E, QuadraticField(-1))));
for p in [3,5] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

printf "rankJ(Q(sqrt-1, sqrt2)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,-1,2,-2]];

"The irreducible factors of \varphi_4/\varphi_2, where \varphi_n is the n-th division polynomial of J, are:";
for f in Factorization(DivisionPolynomial(E, 4) div DivisionPolynomial(E, 2)) do;
    if Exponent(GaloisGroup(f[1])) le 2 then;
        f[1];
    end if;
end for;

"---------------------------------------------";

"For J := the Jacobian of X_1(6,6):";
E := EllipticCurve("36a1");
printf "J(Q(sqrt(-3)))_tors = %o \n", Invariants(TorsionSubgroup(BaseChange(E, QuadraticField(-3))));
for p in [5,7] do;
    Ep := ChangeRing(E, GF(p^2));
    printf "J(F_%o) = %o \n", p^2, Invariants(AbelianGroup(Ep));
end for;

printf "rankJ(Q(sqrt-3)) <= %o \n", &+[RankBound(QuadraticTwist(E,d)) : d in [1,-3]];



/*

///////////////////////////////////////////
//OUTPUT
///////////////////////////////////////////

For J := the Jacobian of X_1(11):
Elliptic Curve defined by y^2 - y = x^3 - x^2 over Rational Field
J(Q)_tors = [ 5 ]
J(F_9) = [ 15 ]
J(F_25) = [ 35 ]
rankJ(Q) <= 0
---------------------------------------------
For J := the Jacobian of X_1(13):
Jacobian of Hyperelliptic Curve defined by y^2 = x^6 - 2*x^5 + x^4 - 2*x^3 +
    6*x^2 - 4*x + 1 over Rational Field
J(Q)_tors = [ 19 ]
J(F_9) = [ 57 ]
J(F_25) = [ 19, 19 ]
rankJ(Q) <= 0
---------------------------------------------
For J := the Jacobian of X_1(14):
Elliptic Curve defined by y^2 + x*y + y = x^3 - x over Rational Field
J(Q)_tors = [ 6 ]
J(F_9) = [ 2, 6 ]
J(F_169) = [ 2, 90 ]
rankJ(Q(sqrt-7)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(15):
Elliptic Curve defined by y^2 + x*y + y = x^3 + x^2 over Rational Field
J(Q)_tors = [ 4 ]
J(F_49) = [ 8, 8 ]
J(F_169) = [ 2, 96 ]
The irreducible factors of varphi_8/varphi_4, where varphi_n is the n-th
division polynomial of J, are:
x^2 - x - 1
x^2 + x + 1
rankJ(Q(sqrt-3, sqrt5)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(16):
Jacobian of Hyperelliptic Curve defined by y^2 = x^5 + 2*x^4 + 2*x^2 - x over
Rational Field
J(Q)_tors = [ 2, 10 ]
J(F_9) = [ 2, 2, 2, 10 ]
J(F_25) = [ 2, 2, 4, 40 ]
rankJ(Q(sqrt-1, sqrt2)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(18):
Jacobian of Hyperelliptic Curve defined by y^2 = x^6 + 2*x^5 + 5*x^4 + 10*x^3 +
    10*x^2 + 4*x + 1 over Rational Field
J(Q)_tors = [ 21 ]
J(F_49) = [ 3, 651 ]
J(F_121) = [ 12, 1092 ]
J^(3)(Q)_tors = [ 3 ]
rankJ(Q(sqrt-3)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(2,10):
Elliptic Curve defined by y^2 = x^3 + x^2 - x over Rational Field
J(Q)_tors = [ 6 ]
J(F_9) = [ 2, 6 ]
J(F_49) = [ 2, 30 ]
rankJ(Q(sqrt5)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(2,12):
Elliptic Curve defined by y^2 = x^3 - x^2 + x over Rational Field
J(Q)_tors = [ 4 ]
J(F_25) = [ 2, 16 ]
J(F_49) = [ 8, 8 ]
The irreducible factors of varphi_8/varphi_4, where varphi_n is the n-th
division polynomial of J, are:
x^2 - 4*x + 1
x^2 + 1
rankJ(Q(sqrt-1, sqrt3)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(3,9):
Elliptic Curve defined by y^2 + y = x^3 over Quadratic Field with defining
polynomial $.1^2 + 3 over the Rational Field
J(Q(sqrt(-3)))_tors = [ 3, 3 ]
J(F_25) = [ 6, 6 ]
J(F_49) = [ 3, 21 ]
rankJ(Q(sqrt-3)) <= 0
---------------------------------------------
For J := the Jacobian of X_1(4,8):
Elliptic Curve defined by y^2 + y = x^3 over Quadratic Field with defining
polynomial $.1^2 + 1 over the Rational Field
J(Q(sqrt(-1)))_tors = [ 2, 4 ]
J(F_9) = [ 4, 4 ]
J(F_25) = [ 4, 8 ]
rankJ(Q(sqrt-1, sqrt2)) <= 0
The irreducible factors of varphi_4/varphi_2, where varphi_n is the n-th
division polynomial of J, are:
x^2 - 2*x - 1
x^2 + 1
x^2 + 2*x - 1
---------------------------------------------
For J := the Jacobian of X_1(6,6):
J(Q(sqrt(-3)))_tors = [ 2, 6 ]
J(F_25) = [ 6, 6 ]
J(F_49) = [ 4, 12 ]
rankJ(Q(sqrt-3)) <= 0



*/




