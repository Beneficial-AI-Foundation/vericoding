// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function bound(x: int): int { if x < 0 then 0 else if x > 4 then 4 else x }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 4 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
    var i := 0;
    sum[0] := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sum[0] <= 4 * i
    {
        sum[0] := sum[0] + bound(a[i]);
        i := i + 1;
    }
}
// </vc-code>
