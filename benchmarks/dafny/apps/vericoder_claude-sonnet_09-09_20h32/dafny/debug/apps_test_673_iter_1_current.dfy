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
    
    // Prove next > n
    assert next == ((n / k) + 1) * k;
    assert next == (n / k) * k + k;
    assert (n / k) * k <= n < ((n / k) + 1) * k by {
        assert n / k * k <= n;
        assert n < (n / k + 1) * k;
    }
    
    // Prove next % k == 0
    assert next % k == (((n / k) + 1) * k) % k == 0;
    
    // Prove forall x :: n < x < next ==> x % k != 0
    forall x | n < x < next
        ensures x % k != 0
    {
        assert x < ((n / k) + 1) * k;
        assert x <= (n / k) * k + k - 1;
        if x % k == 0 {
            assert x == (x / k) * k;
            assert x / k <= n / k by {
                if x / k > n / k {
                    assert x >= (n / k + 1) * k;
                    assert false;
                }
            }
            assert x <= (n / k) * k;
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

