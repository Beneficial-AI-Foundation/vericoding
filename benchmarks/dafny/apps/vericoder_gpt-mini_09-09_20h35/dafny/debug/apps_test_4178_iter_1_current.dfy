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
// No additional helpers needed.
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: string)
  requires ValidInput(n, heights)
  ensures result == "Yes" <==> CanMakeNonDecreasing(heights)
// </vc-spec>
// <vc-code>
{
  var prevMax := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant prevMax == maxHeightUpTo(heights, i - 1)
    invariant forall j :: 0 <= j < i ==> heights[j] >= maxHeightUpTo(heights, j) - 1
    decreases n - i
  {
    if heights[i] < prevMax - 1 {
      // witness that CanMakeNonDecreasing is false at position i
      assert maxHeightUpTo(heights, i) == (if heights[i] > prevMax then heights[i] else prevMax);
      // since heights[i] < prevMax the above evaluates to prevMax
      assert heights[i] < maxHeightUpTo(heights, i) - 1;
      result := "No";
      return;
    }
    if heights[i] > prevMax {
      prevMax := heights[i];
    }
    i := i + 1;
  }
  // Invariant gives the property for all positions
  result := "Yes";
}
// </vc-code>

