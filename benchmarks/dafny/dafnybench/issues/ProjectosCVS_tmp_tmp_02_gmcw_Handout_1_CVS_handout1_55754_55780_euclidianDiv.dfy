// <vc-preamble>
/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

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



//Second Exercise
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
// </vc-spec>
// <vc-code>
{
        r := a;
        q := 0;
        while(r - b >= 0)
            decreases r - b
            invariant 0 <= r <= a
            // invariant a == b * q + r
            invariant r == a - b * q
        {
            r := r - b;
            q := q + 1;
        }
}
// </vc-code>
