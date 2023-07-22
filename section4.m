

/*
202307200104
The code verifying the proofs of theorem 4.7.
*/



///////////////////////////////////////////
//INPUT
///////////////////////////////////////////


F := ExtensionField< FiniteField(3), x | x^2 + 1 >;

TheList := [];
for a,b,c in F do;
if IsEllipticCurve([0, a, 0, b, c]) then;
    E := EllipticCurve([0, a, 0, b, c]);
    G := AbelianGroup(E);
    if &or[IsDivisibleBy(d, 16) : d in Invariants(G)] then;
        TheList := Append(TheList, E);
    end if;
end if;
end for;

if #TheList eq 0 then;
    "There are no elliptic curves over F_9 which contains Z/16.";
else;
    "The following elliptic curves over F_9 contain Z/16:";
    TheList;
end if;

/*

///////////////////////////////////////////
//OUTPUT
///////////////////////////////////////////

There are no elliptic curves over F_9 which contains Z/16.

*/




