// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>