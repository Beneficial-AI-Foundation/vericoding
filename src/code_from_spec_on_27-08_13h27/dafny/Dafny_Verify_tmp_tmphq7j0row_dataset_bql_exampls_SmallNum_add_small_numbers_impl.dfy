// <vc-helpers>
// No additional helpers or proofs needed for this implementation
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
method AddSmallNumbers(a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0
    requires n <= a.Length
    requires forall i: int :: 0 <= i && i < n ==> a[i] <= max
    ensures r <= max * n
{
    r := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant r <= max * i
    {
        r := r + a[i];
        i := i + 1;
    }
}
// </vc-code>
