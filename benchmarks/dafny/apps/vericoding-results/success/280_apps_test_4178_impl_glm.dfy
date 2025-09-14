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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: string)
  requires ValidInput(n, heights)
  ensures result == "Yes" <==> CanMakeNonDecreasing(heights)
// </vc-spec>
// <vc-code>
{
  var current_max: int := 0;
  var i: int := 0;
  while i < |heights|
    invariant 0 <= i <= |heights|
    invariant current_max == (if i==0 then 0 else maxHeightUpTo(heights, i-1))
    invariant forall k :: 0 <= k < i ==> heights[k] >= maxHeightUpTo(heights, k) - 1
  {
    if heights[i] > current_max {
        current_max := heights[i];
    } else if heights[i] < current_max - 1 {
        return "No";
    }
    i := i + 1;
  }
  return "Yes";
}
// </vc-code>

