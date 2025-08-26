/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

// First Exercise
// <vc-spec>
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

// <vc-helpers>
// </vc-helpers>

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
// </vc-spec>
// <vc-code>
{
    r := 0;
    var x := a;
    var y := b;
    
    while y > 0
        invariant r + x * y == a * b
        invariant y >= 0
        decreases y
    {
        if y % 2 == 1 {
            r := r + x;
            peasantMultLemma(x, y);
        } else {
            peasantMultLemma(x, y);
        }
        x := 2 * x;
        y := y / 2;
    }
}
// </vc-code>

//Second Exercise