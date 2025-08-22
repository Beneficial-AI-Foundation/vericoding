//IMPL Divby2
/* code modified by LLM (iteration 4): fixed helper lemma proofs and corrected base case */
lemma EvenTimesAnything(a: nat, b: nat)
requires a % 2 == 0
ensures (a * b) % 2 == 0
{
    // Since a is even, a = 2k for some k
    // So a * b = 2k * b = 2 * (k * b), which is even
    var k := a / 2;
    assert a == 2 * k;
    assert a * b == 2 * k * b;
    assert a * b == 2 * (k * b);
    assert (a * b) % 2 == 0;
}

lemma AnythingTimesEven(a: nat, b: nat)
requires b % 2 == 0
ensures (a * b) % 2 == 0
{
    // Since b is even, b = 2k for some k
    // So a * b = a * 2k = 2 * (a * k), which is even
    var k := b / 2;
    assert b == 2 * k;
    assert a * b == a * 2 * k;
    assert a * b == 2 * (a * k);
    assert (a * b) % 2 == 0;
}

lemma Divby2(n: nat)
ensures (n*(n-1))%2 == 0
{
    /* code modified by LLM (iteration 4): corrected base case and strengthened proof */
    if n == 0 {
        // Base case: when n=0, n-1 in nat arithmetic becomes 0 (underflow protection)
        // So n*(n-1) = 0*0 = 0, and 0%2 == 0
        assert n - 1 == 0;  // nat arithmetic: 0-1 = 0
        assert n * (n-1) == 0;
        assert 0 % 2 == 0;
    } else if n % 2 == 0 {
        // Case: n is even and n > 0
        // Since n is even, n*(n-1) is even
        EvenTimesAnything(n, n-1);
        assert (n * (n-1)) % 2 == 0;
    } else {
        // Case: n is odd and n > 0
        // If n is odd, then n-1 is even, so n*(n-1) is even
        assert n % 2 == 1;
        assert n >= 1;
        assert (n-1) % 2 == 0;
        AnythingTimesEven(n, n-1);
        assert (n * (n-1)) % 2 == 0;
    }
}