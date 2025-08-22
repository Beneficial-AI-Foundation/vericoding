// program verifies
// ATOM 
function expo(x:int, n:nat): int
{
    if n == 0 then 1
    else x * expo(x, n-1)
}

/* code modified by LLM (iteration 4): Fixed helper lemma with proper proof */
lemma ModularArithmetic(a: int, b: int, m: int)
requires m > 0
requires a % m == 0
requires b % m == 0
ensures (a + b) % m == 0
{
    // Since a % m == 0, we have a == k1 * m for some integer k1
    // Since b % m == 0, we have b == k2 * m for some integer k2
    // Therefore a + b == (k1 + k2) * m
    // So (a + b) % m == 0
    assert (a + b) % m == (a % m + b % m) % m;
    assert (a % m + b % m) % m == (0 + 0) % m;
    assert (0 + 0) % m == 0;
}

/* code modified by LLM (iteration 4): Fixed helper lemma with proper proof */
lemma ModularMultiplication(a: int, k: int, m: int)
requires m > 0
requires a % m == 0
ensures (k * a) % m == 0
{
    // If a % m == 0, then a = q * m for some integer q
    // So k * a = k * q * m = (k * q) * m
    // Therefore (k * a) % m == 0
    assert (k * a) % m == (k % m * a % m) % m;
    assert (k % m * a % m) % m == (k % m * 0) % m;
    assert (k % m * 0) % m == 0;
}

//IMPL Expon23
lemma Expon23(n: nat)
requires n >= 0
ensures ((expo(2,3*n) - expo(3,n)) % (2+3)) == 0
{   
    /* code modified by LLM (iteration 4): Restructured proof with direct calculation */
    if (n == 0) {
        // Base case: expo(2,0) - expo(3,0) = 1 - 1 = 0
        assert expo(2, 0) == 1;
        assert expo(3, 0) == 1;
        assert expo(2, 0) - expo(3, 0) == 0;
        assert 0 % 5 == 0;
    }
    else {
        /* code modified by LLM (iteration 4): Inductive step with corrected modular arithmetic */
        Expon23(n-1); // Inductive hypothesis
        
        // Inductive hypothesis: (expo(2, 3*(n-1)) - expo(3, n-1)) % 5 == 0
        var prev_2 := expo(2, 3*(n-1));
        var prev_3 := expo(3, n-1);
        assert (prev_2 - prev_3) % 5 == 0;
        
        // Current values
        var curr_2 := expo(2, 3*n);
        var curr_3 := expo(3, n);
        
        // Express in terms of previous values
        assert curr_2 == prev_2 * expo(2, 3);
        assert expo(2, 3) == 8;
        assert curr_2 == prev_2 * 8;
        
        assert curr_3 == prev_3 * expo(3, 1);
        assert expo(3, 1) == 3;
        assert curr_3 == prev_3 * 3;
        
        // Calculate the difference
        var diff := curr_2 - curr_3;
        assert diff == prev_2 * 8 - prev_3 * 3;
        
        /* code modified by LLM (iteration 4): Direct algebraic manipulation */
        // Rewrite: 8*prev_2 - 3*prev_3 = 8*prev_2 - 8*prev_3 + 5*prev_3
        //                                = 8*(prev_2 - prev_3) + 5*prev_3
        calc {
            diff;
        ==  prev_2 * 8 - prev_3 * 3;
        ==  prev_2 * 8 - prev_3 * 8 + prev_3 * 8 - prev_3 * 3;
        ==  8 * (prev_2 - prev_3) + prev_3 * (8 - 3);
        ==  8 * (prev_2 - prev_3) + prev_3 * 5;
        }
        
        // Apply modular arithmetic
        ModularMultiplication(prev_2 - prev_3, 8, 5);
        assert (8 * (prev_2 - prev_3)) % 5 == 0;
        
        assert (prev_3 * 5) % 5 == 0;
        
        ModularArithmetic(8 * (prev_2 - prev_3), prev_3 * 5, 5);
        assert (8 * (prev_2 - prev_3) + prev_3 * 5) % 5 == 0;
        assert diff % 5 == 0;
    }
}