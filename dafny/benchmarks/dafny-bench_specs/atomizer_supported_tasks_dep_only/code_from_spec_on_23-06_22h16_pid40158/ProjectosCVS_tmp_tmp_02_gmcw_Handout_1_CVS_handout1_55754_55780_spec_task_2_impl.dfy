/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

// First Exercise
//ATOM_PLACEHOLDER_peasantMultLemma

//ATOM_PLACEHOLDER_peasantMult


//Second Exercise
// SPEC 


//IMPL Second Exercise
method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
    ensures 0 <= r < b
    {
        q := 0;
        r := a;
        
        while r >= b
            invariant a == b * q + r
            invariant r >= 0
            decreases r
        {
            q := q + 1;
            r := r - b;
        }
    }