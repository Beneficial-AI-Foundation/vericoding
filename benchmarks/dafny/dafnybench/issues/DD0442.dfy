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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
// </vc-spec>
// <vc-code>
{
        r := 0;
        var aa := a;
        var bb := b;

        while(bb > 0)
            decreases bb 
            invariant 0 <= bb <= b
            invariant r + aa * bb == a * b
        { 
            // Use of lemma was not necessary for a successful verification
            // peasantMultLemma(aa, bb);
            if (bb % 2 == 0)
            {
                aa := 2 * aa;
                bb := bb / 2;

            } else if (bb % 2 == 1)
            {
                r := r + aa;
                aa := 2 * aa;
                bb := (bb-1) / 2;
            }
        } 
}
// </vc-code>

//Second Exercise