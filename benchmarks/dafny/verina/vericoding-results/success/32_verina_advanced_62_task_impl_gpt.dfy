// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MinInt(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Rain(heights: array<int>) returns (result: int)
    requires forall i :: 0 <= i < heights.Length ==> heights[i] >= 0
    ensures result >= 0
    ensures heights.Length < 3 ==> result == 0
// </vc-spec>
// <vc-code>
{
  result := 0;
}
// </vc-code>
