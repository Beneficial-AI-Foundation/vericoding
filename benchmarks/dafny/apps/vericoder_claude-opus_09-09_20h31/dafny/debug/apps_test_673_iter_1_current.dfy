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
    DivModProperty(n, k);
    assert result == (n / k) * k + k;
    assert result > (n / k) * k + (n % k);
    assert result > n;
    assert result % k == 0;
}

lemma NoSmallerMultiple(n: int, k: int)
    requires n >= 1 && k > 0
    ensures var result := (n / k + 1) * k;
            forall x :: n < x < result ==> x % k != 0
{
    var result := (n / k + 1) * k;
    DivModProperty(n, k);
    
    forall x | n < x < result
        ensures x % k != 0
    {
        if x % k == 0 {
            assert exists m :: x == m * k;
            var m := x / k;
            assert x == m * k;
            assert n < m * k < result;
            assert n < m * k < (n / k + 1) * k;
            assert n / k < m < n / k + 1;
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

