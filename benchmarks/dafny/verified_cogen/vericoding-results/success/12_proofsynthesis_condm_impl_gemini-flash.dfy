// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    ensures forall k:int :: 0 <= k < N ==> a[k] % 2 == N % 2
    modifies a
// </vc-spec>
// <vc-code>
{
    var k := 0;
    while k < N
        invariant 0 <= k <= N
        invariant forall i: int :: 0 <= i < k ==> a[i] % 2 == N % 2
    {
        if N % 2 == 0 {
            a[k] := 2 * (a[k] / 2);
        } else {
            a[k] := 2 * (a[k] / 2) + 1;
        }
        k := k + 1;
    }
}
// </vc-code>
