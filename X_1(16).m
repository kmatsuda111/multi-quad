
/*
the proof of lemma 5.4 for N = 16.
*/


function OrderC(P)
	zfunc:=0;
	repeat zfunc:=zfunc+1; until IsZero(zfunc*P); 
	return zfunc;
end function;

n := 16;

_<x>:=PolynomialRing(Rationals());
K<a,b> := NumberField([x^2 + 1, x^2 - 2]);
_<x>:=PolynomialRing(K);

X := HyperellipticCurve(x * (x^2 + 1) * (x^2 + 2*x - 1));
// X_1(16);

ptsQ := [ X![1,0,0], X![0,0,1], X![1,2,1], X![1,-2,1], X![-1,2,1], X![-1,-2,1]];
ptsQa := [ X![a,0,1], X![-a,0,1] ];
ptsQb := [X![-1 + b,0,1], X![-1-b,0,1]];
pts := ptsQ cat ptsQa cat ptsQb;
assert #pts eq 10;
// X(K) = union of them.

inf := ptsQ[1];

D1 := ptsQ[2] - inf;
// OrderC(D1);
// This is = 2.
D2 := ptsQ[3] - inf;
// OrderC(D2);
// This is = 10.

// JQ := { i1*D1 + i2 * D2 : i1 in [0..1], i2 in [0..9] };
// #JQ;
// // This is = 20, which is = #J_1(16)(Q).
// // So J_1(16)(Q) = [2,10] = <D1, D2>.

D3 := ptsQa[1] - inf;
// OrderC(D3);
// This is = 2.

D4 := ptsQb[1] - inf;
// OrderC(D4);
// This is = 2.

// So J_1(16)(K) = [2,10,2,2] = <D1, D2, D3, D4>.

JT := { i1*D1 + i2 * D2 + i3 * D3 + i4 * D4 :
i1 in [0..1], i2 in [0..9], i3 in [0..1], i4 in [0..1] };
assert #JT eq 80;
assert &and[IsDivisibleBy(D[2]^2 - x * (x^2 + 1) * (x^2 + 2*x - 1), D[1]) : D in JT ]
and &and[Degree(D[2]) lt Degree(D[1]) and Degree(D[1]) le 2  : D in JT ];

ss := {@ [D[1], D[2]] : D in JT | Degree(D[1]) eq 2 and IsIrreducible(D[1]) @};
// The set of quadratic points of X_K not in ``the line" corresponds to
// ss by P \mapsto P + P~ - 2\infty, where P~ is the conjugate.
"The number of quadratic points of X_K not in the line is:", #ss;

"For every such a point P, the field K(P) is not multi-quadratic over Q:",
&and[ Exponent(GaloisGroup(AbsoluteField(NumberField(D[1])))) ne 2
: D in ss ];
// Check, for every quadratic point P of X_K not in ``the line",
// the whether K(P)/\Q is quadratic or not.


/*

/////////////////////////////////////
//OUTPUT
/////////////////////////////////////

The number of quadratic points of X_K not in the line is: 32
For every such a point P, the field K(P) is not multi-quadratic over Q: true

*/