
/*
the proof of lemma 5.4 for N = 18.
*/


function OrderC(P)
	zfunc:=0;
	repeat zfunc:=zfunc+1; until IsZero(zfunc*P); 
	return zfunc;
end function;

n := 18;

_<x>:=PolynomialRing(Rationals());
K<a> := NumberField(x^2 + 3);
_<x>:=PolynomialRing(K);

X := HyperellipticCurve(x^6 + 2*x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 4*x + 1);
// X_1(18);

ptsQ := [ X![1,1,0], X![1,-1,0], X![0,1,1], X![0,-1,1], X![-1,1,1], X![-1,-1,1]];
ptsQa := [ X![1/2*(a - 1),1/2*(a - 3),1], X![1/2*(a - 1),1/2*(-a + 3),1],
 X![1/2*(-a - 1),1/2*(a + 3),1], X![1/2*(-a - 1),1/2*(-a - 3),1]];
pts := ptsQ cat ptsQa;
assert #pts eq 10;
// X(K) = union of their.

inf := ptsQ[1];

D1 := ptsQ[2] - inf;
// OrderC(D1);
// = 21. Hence J(Q) = [21] = <D1>.
D2 := (ptsQa[1] - inf) - 4*D1;
// OrderC(D2);
// = 3.
// Since genus >= 2, this is not over Q.
// Hence J(K) = [21, 3] = <D1, D2>.

JT := { i1*D1 + i2 * D2 :
i1 in [0..20], i2 in [0..2]};
assert #JT eq 63;
assert &and[IsDivisibleBy(D[2]^2 - (x^6 + 2*x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 4*x + 1), D[1]) : D in JT ];

ss := {@ [D[1], D[2]] : D in JT | Degree(D[1]) eq 2 and IsIrreducible(D[1]) @};
// The set of quadratic points of X_K not in ``the line" corresponds to
// ss by P \mapsto P + P~ - \infty1 - \infty2, where P~ is the conjugate.
"The number of quadratic points of X_K not in the line is:", #ss;

"For every such a point P, the field K(P) is not multi-quadratic over Q:",
&and[ Exponent(GaloisGroup(AbsoluteField(NumberField(D[1])))) ne 2 : D in ss ];
// Check, for every quadratic point P of X_K not in ``the line",
// the whether K(P)/\Q is quadratic or not.

/*

/////////////////////////////////////
//OUTPUT
/////////////////////////////////////

The number of quadratic points of X_K not in the line is: 12
For every such a point P, the field K(P) is not multi-quadratic over Q: true

*/