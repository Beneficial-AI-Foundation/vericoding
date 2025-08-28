function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
lemma SumIntsFormula(n: int)
    requires n >= 0
    ensures sumInts(n) == n * (n + 1) / 2
{
    if n == 0 {
        assert sumInts(0) == 0;
        assert 0 * (0 + 1) / 2 == 0;
    } else {
        SumIntsFormula(n - 1);
        assert sumInts(n - 1) == (n - 1) * n / 2;
        assert sumInts(n) == sumInts(n - 1) + n;
        assert sumInts(n) == (n - 1) * n / 2 + n;
        assert sumInts(n) == (n - 1) * n / 2 + 2 * n / 2;
        assert sumInts(n) == ((n - 1) * n + 2 * n) / 2;
        assert sumInts(n) == (n * n - n + 2 * n) / 2;
        assert sumInts(n) == (n * n + n) / 2;
        assert sumInts(n) == n * (n + 1) / 2;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    s := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant s == sumInts(i)
    {
        i := i + 1;
        s := s + i;
    }
    
    SumIntsFormula(n);
}
// </vc-code>
