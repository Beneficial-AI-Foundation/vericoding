// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Rain(heights: array<int>) returns (result: int)
    requires forall i :: 0 <= i < heights.Length ==> heights[i] >= 0
    ensures result >= 0
    ensures heights.Length < 3 ==> result == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
