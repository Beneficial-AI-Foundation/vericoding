// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 5 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
    for i := 0 to N-1
        invariant 0 <= i <= N
        invariant forall j: int :: 0 <= j < i ==> a[j] == 5
    {
        a[i] := 5;
    }
    sum[0] := 5 * N;
}
// </vc-code>
