// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
    decreases t - s
{
    if s < 0 || s >= t || t > |a| then
        0
    else
        a[t - 1] + Sum(a, s, t - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxSegmentSum(a: array<int>, s: int, t: int) returns (p: (int, int))
    ensures
        var (i, j) := p; 0 <= i <= j <= a.Length
    ensures
        var (i, j) := p; forall k: int, l: int :: 0 <= k <= l <= a.Length ==> Sum(a[..], k, l) <= Sum(a[..], i, j)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
