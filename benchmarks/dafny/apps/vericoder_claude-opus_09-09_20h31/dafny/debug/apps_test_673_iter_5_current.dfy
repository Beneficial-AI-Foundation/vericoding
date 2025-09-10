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
lemma DivModProperty(n: int, k: int)
    requires k > 0
    ensures n == (n / k) * k + (n % k)
    ensures 0 <= n % k < k
{
}

lemma NextMultipleIsCorrect(n: int, k: int)
    requires n >= 1 && k > 0
    ensures var result := (n / k + 1) * k;
            result > n && result % k == 0
{
    var result := (n / k + 1) * k;
    assert result % k == 0;
    assert result == (n / k) * k + k;
    assert n / k * k <= n;
    assert result > n;
}

lemma NoSmallerMultiple(n: int, k: int)
    requires n >= 1 && k > 0
    ensures var result := (n / k + 1) * k;
            forall x :: n < x < result ==> x % k != 0
{
    var result := (n / k + 1) * k;
    var q := n / k;
    assert result == (q + 1) * k;
    
    forall x | n < x < result
        ensures x % k != 0
    {
        // x is between n and the next multiple of k after n
        // The only multiple of k in range [q*k, (q+1)*k] is at the boundaries
        assert q * k <= n < (q + 1) * k;
        assert x < (q + 1) * k;
        
        if x % k == 0 {
            // x must be some multiple m*k
            var m := x / k;
            assert x == m * k;
            assert n < m * k < (q + 1) * k;
            // This means q < m < q + 1, which is impossible for integers
            assert m <= q || m >= q + 1;
            assert m * k <= q * k || m * k >= (q + 1) * k;
            assert m * k <= n || m * k >= result;
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
    result := (n / k + 1) * k;
    
    NextMultipleIsCorrect(n, k);
    NoSmallerMultiple(n, k);
}
// </vc-code>

