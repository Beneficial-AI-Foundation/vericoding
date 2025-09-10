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
lemma MaxHeightUpToMonotonic(heights: seq<int>, i: int, j: int)
  requires |heights| > 0
  requires -1 <= i <= j < |heights|
  ensures maxHeightUpTo(heights, i) <= maxHeightUpTo(heights, j)
{
  if i == j {
    // Base case: trivially true
  } else if i < 0 {
    // maxHeightUpTo(heights, i) == 0, and maxHeightUpTo(heights, j) >= 0
    assert maxHeightUpTo(heights, i) == 0;
    MaxHeightUpToProperties(heights, j);
  } else {
    // Inductive case
    MaxHeightUpToMonotonic(heights, i, j - 1);
    assert maxHeightUpTo(heights, i) <= maxHeightUpTo(heights, j - 1);
    assert maxHeightUpTo(heights, j - 1) <= maxHeightUpTo(heights, j);
  }
}

lemma MaxHeightUpToProperties(heights: seq<int>, index: int)
  requires |heights| > 0
  requires 0 <= index < |heights|
  ensures maxHeightUpTo(heights, index) >= heights[index]
  ensures maxHeightUpTo(heights, index) >= 0
  ensures forall i :: 0 <= i <= index ==> heights[i] <= maxHeightUpTo(heights, index)
{
  if index == 0 {
    // Base case
  } else {
    MaxHeightUpToProperties(heights, index - 1);
    if heights[index] > maxHeightUpTo(heights, index - 1) {
      // maxHeightUpTo(heights, index) == heights[index]
    } else {
      // maxHeightUpTo(heights, index) == maxHeightUpTo(heights, index - 1)
    }
  }
}

lemma MaxHeightUpToNonNegative(heights: seq<int>, index: int)
  requires ValidInput(|heights|, heights)
  requires -1 <= index < |heights|
  ensures maxHeightUpTo(heights, index) >= 0
{
  if index < 0 {
    assert maxHeightUpTo(heights, index) == 0;
  } else if index == 0 {
    assert maxHeightUpTo(heights, index) == heights[0];
    assert heights[0] >= 1;
  } else {
    MaxHeightUpToNonNegative(heights, index - 1);
    assert maxHeightUpTo(heights, index - 1) >= 0;
    if heights[index] > maxHeightUpTo(heights, index - 1) {
      assert maxHeightUpTo(heights, index) == heights[index];
      assert heights[index] >= 1;
    } else {
      assert maxHeightUpTo(heights, index) == maxHeightUpTo(heights, index - 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: string)
  requires ValidInput(n, heights)
  ensures result == "Yes" <==> CanMakeNonDecreasing(heights)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> heights[j] >= maxHeightUpTo(heights, j) - 1
  {
    MaxHeightUpToProperties(heights, i);
    MaxHeightUpToNonNegative(heights, i);
    if heights[i] < maxHeightUpTo(heights, i) - 1 {
      return "No";
    }
    i := i + 1;
  }
  return "Yes";
}
// </vc-code>

