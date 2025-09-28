// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Rain(heights: array<int>) returns (result: int)
    requires forall i :: 0 <= i < heights.Length ==> heights[i] >= 0
    ensures result >= 0
    ensures heights.Length < 3 ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [Added invariant to carry left_max property across a loop] */
    var n := heights.Length;
    if n < 3 {
        result := 0;
        return;
    }

    var left_max := new int[n];
    left_max[0] := heights[0];
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> left_max[j] >= heights[j]
    {
        left_max[i] := max(left_max[i-1], heights[i]);
        i := i + 1;
    }

    var right_max := new int[n];
    right_max[n-1] := heights[n-1];
    var j := n - 2;
    while j >= 0
        invariant -1 <= j <= n-2
        invariant forall k :: j < k < n ==> right_max[k] >= heights[k]
        invariant forall m :: 0 <= m < n ==> left_max[m] >= heights[m]
    {
        right_max[j] := max(right_max[j+1], heights[j]);
        j := j - 1;
    }

    result := 0;
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant result >= 0
        invariant forall m :: 0 <= m < n ==> left_max[m] >= heights[m]
        invariant forall m :: 0 <= m < n ==> right_max[m] >= heights[m]
    {
        var water := min(left_max[k], right_max[k]) - heights[k];
        result := result + water;
        k := k + 1;
    }
}
// </vc-code>
