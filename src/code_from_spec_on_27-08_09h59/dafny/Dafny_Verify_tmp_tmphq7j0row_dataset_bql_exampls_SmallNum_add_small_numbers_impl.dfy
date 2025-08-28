// <vc-helpers>
lemma SumBound(a: array<int>, n: int, max: int, sum: int)
    requires n >= 0
    requires n <= a.Length
    requires forall i: int :: 0 <= i < n ==> a[i] <= max
    requires sum == SumArray(a, n)
    ensures sum <= max * n
{
    if n == 0 {
        assert sum == 0;
        assert max * n == 0;
    } else {
        assert sum == SumArray(a, n-1) + a[n-1];
        SumBound(a, n-1, max, SumArray(a, n-1));
        assert SumArray(a, n-1) <= max * (n-1);
        assert a[n-1] <= max;
        assert sum <= max * (n-1) + max;
        assert sum <= max * n;
    }
}

function SumArray(a: array<int>, n: int): int
    requires 0 <= n <= a.Length
    reads a
{
    if n == 0 then 0 else SumArray(a, n-1) + a[n-1]
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var sum := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant sum == SumArray(a, i)
        invariant sum <= max * i
    {
        sum := sum + a[i];
        i := i + 1;
    }
    
    SumBound(a, n, max, sum);
    return sum;
}
// </vc-code>
