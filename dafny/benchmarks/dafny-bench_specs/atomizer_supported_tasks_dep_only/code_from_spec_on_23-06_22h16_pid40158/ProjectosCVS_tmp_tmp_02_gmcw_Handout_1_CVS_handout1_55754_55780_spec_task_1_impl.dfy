/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

// First Exercise
//ATOM peasantMultLemma
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
            decreases y
        {
            if y % 2 == 1 {
                /* code modified by LLM (iteration 1): add x to result and decrement y */
                r := r + x;
                y := y - 1;
            } else {
                /* code modified by LLM (iteration 1): double x and halve y for even case */
                x := 2 * x;
                y := y / 2;
            }
        }
    }



//Second Exercise
//ATOM euclidianDiv