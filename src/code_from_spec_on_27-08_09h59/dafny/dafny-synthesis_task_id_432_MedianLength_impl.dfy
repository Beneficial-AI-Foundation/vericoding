// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  median := (a + b) / 2;
}
// </vc-code>
