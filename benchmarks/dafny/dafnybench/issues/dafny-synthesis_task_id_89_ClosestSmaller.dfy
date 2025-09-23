// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
// </vc-spec>
// <vc-code>
{
    m := n - 1;
}
// </vc-code>
