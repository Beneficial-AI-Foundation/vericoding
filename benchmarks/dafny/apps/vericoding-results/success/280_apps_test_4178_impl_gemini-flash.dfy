// <vc-preamble>
function maxHeightUpTo(heights: seq<int>, index: int): int
  requires |heights| > 0
  requires -1 <= index < |heights|
{
  if index < 0 then 0
  else if index == 0 then heights[0]
  else if heights[index] > maxHeightUpTo(heights, index - 1) 
    then heights[index]
    else maxHeightUpTo(heights, index - 1)
}

predicate ValidInput(n: int, heights: seq<int>)
{
  n >= 1 && |heights| == n && (forall i :: 0 <= i < |heights| ==> heights[i] >= 1)
}

predicate CanMakeNonDecreasing(heights: seq<int>)
  requires |heights| > 0
{
  forall i :: 0 <= i < |heights| ==> heights[i] >= maxHeightUpTo(heights, i) - 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section is intentionally left empty. */
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: string)
  requires ValidInput(n, heights)
  ensures result == "Yes" <==> CanMakeNonDecreasing(heights)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Reworking the loop to directly calculate the `CanMakeNonDecreasing` condition. The loop invariant now explicitly relates `maxSoFar` to `maxHeightUpTo` and also includes the condition for `CanMakeNonDecreasing` for the elements processed so far. */
{
  var maxSoFar := 0;
  for i := 0 to n
    invariant 0 <= i <= n
    invariant (forall k :: 0 <= k < i ==> heights[k] >= maxHeightUpTo(heights, k) - 1)
    invariant maxSoFar == maxHeightUpTo(heights, i-1)
  {
    if i == n { break; }
    if heights[i] < maxSoFar - 1 {
      result := "No";
      return;
    }
    if heights[i] > maxSoFar {
      maxSoFar := heights[i];
    }
  }
  result := "Yes";
}
// </vc-code>
