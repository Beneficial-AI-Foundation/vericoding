// <vc-preamble>
predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
    ensures MaxInSeq(s) in s
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxInSeq(s)
{
    if |s| == 1 then s[0]
    else
        var tailMax := MaxInSeq(s[1..]);
        if s[0] >= tailMax then s[0] else tailMax
}

predicate ValidResult(n: int, heights: seq<int>, result: int)
    requires ValidInput(n, heights)
{
    result == MaxInSeq(heights) &&
    forall i :: 0 <= i < |heights| ==> heights[i] <= result &&
    exists i :: 0 <= i < |heights| && heights[i] == result
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
function Min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: int)
    requires ValidInput(n, heights)
    ensures ValidResult(n, heights, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous implementation for `currentMax` was incorrect. This version correctly updates `currentMax` with `MaxInSeq` ensuring the invariant `currentMax == MaxInSeq(heights[0..i])` holds at each step. Also, corrected the assignment to take max of currentMax and heights[i] to fix compile warning. */
{
  var currentMax := heights[0];
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> heights[j] <= currentMax
    invariant exists k :: 0 <= k < i && heights[k] == currentMax
    invariant currentMax == MaxInSeq(heights[0..i])
  {
    currentMax := MaxInSeq([currentMax, heights[i]]);
    i := i + 1;
  }
  result := currentMax;
}
// </vc-code>
