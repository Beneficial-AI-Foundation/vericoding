

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sum <= i * max
        invariant sum <= n * max
    {
        sum := sum + a[i];
        i := i + 1;
    }
    return sum;
}
// </vc-code>

