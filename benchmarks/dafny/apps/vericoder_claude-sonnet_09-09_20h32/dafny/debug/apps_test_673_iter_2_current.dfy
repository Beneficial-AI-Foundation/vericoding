predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
lemma NextMultipleIsCorrect(n: int, k: int)
    requires k > 0 && n >= 1
    ensures var next := ((n / k) + 1) * k;
            next > n && next % k == 0 && forall x :: n < x < next ==> x % k != 0
{
    var next := ((n / k) + 1) * k;
    var q := n / k;
    
    // Prove next > n
    assert next == (q + 1) * k;
    assert q * k <= n < (q + 1) * k;
    assert next > n;
    
    // Prove next % k == 0
    assert next % k == 0;
    
    // Prove forall x :: n < x < next ==> x % k != 0
    forall x | n < x < next
        ensures x % k != 0
    {
        if x % k == 0 {
            var xq := x / k;
            assert x == xq * k;
            assert xq * k < (q + 1) * k;
            assert xq <= q;
            assert x <= q * k;
            assert x <= n;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
    result := ((n / k) + 1) * k;
    NextMultipleIsCorrect(n, k);
}
// </vc-code>

