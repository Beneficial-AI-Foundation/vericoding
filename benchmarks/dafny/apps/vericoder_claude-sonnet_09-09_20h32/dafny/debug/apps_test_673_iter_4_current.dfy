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
    
    // next > n
    assert next == (q + 1) * k;
    assert q * k <= n < (q + 1) * k;
    assert next > n;
    
    // next % k == 0
    assert next % k == 0;
    
    // No multiple of k between n and next
    forall x | n < x < next && x % k == 0
        ensures false
    {
        var xq := x / k;
        assert x == xq * k;
        assert xq * k <= n ==> xq <= q;
        assert x > n && xq * k <= n ==> false;
        assert xq >= q + 1;
        assert x >= (q + 1) * k == next;
        assert false;
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

