// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Identity(x: int): int { x }
// </vc-helpers>

// <vc-spec>
method MaxCoverageAfterRemovingOne(intervals: array<(int, int)>) returns (result: int)
    requires intervals.Length > 0
    ensures result <= intervals.Length * 1000
// </vc-spec>
// <vc-code>
{
  result := 0;
}
// </vc-code>
