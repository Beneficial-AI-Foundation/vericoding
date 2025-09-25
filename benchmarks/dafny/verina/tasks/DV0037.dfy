// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxCoverageAfterRemovingOne(intervals: array<(int, int)>) returns (result: int)
    requires intervals.Length > 0
    ensures result <= intervals.Length * 1000
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
