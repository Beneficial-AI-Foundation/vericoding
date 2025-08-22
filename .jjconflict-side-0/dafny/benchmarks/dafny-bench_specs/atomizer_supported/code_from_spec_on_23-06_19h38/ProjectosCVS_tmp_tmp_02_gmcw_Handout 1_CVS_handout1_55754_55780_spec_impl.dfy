/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

// First Exercise
// ATOM 

// First Exercise
lemma peasantMultLemma(a:int, b:int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
    {
        if (b % 2 == 0 && b > 0) { 
            peasantMultLemma(a, b - 2);
        }

        if (b % 2 == 1 && b > 1) {
            peasantMultLemma(a, b - 2);
        }

    }


//IMPL peasantMult

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
    {
        var x := a;
        var y := b;
        r := 0;
        
        while y > 0
            invariant r + x * y == a * b
            invariant y >= 0
            decreases y
        {
            if y % 2 == 1 {
                r := r + x;
            }
            peasantMultLemma(x, y);
            x := 2 * x;
            y := y / 2;
        }
    }



//Second Exercise
//IMPL euclidianDiv


//Second Exercise
method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
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