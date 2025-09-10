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
lemma MaxHeightUpToLemma(heights: seq<int>, i: int, j: int)
  requires |heights| > 0
  requires -1 <= i <= j < |heights|
  ensures maxHeightUpTo(heights, i) <= maxHeightUpTo(heights, j)
{
  if i < j {
    MaxHeightUpToLemma(heights, i, j - 1);
    if heights[j] > maxHeightUpTo(heights, j - 1) {
      assert maxHeightUpTo(heights, j) == heights[j];
      assert maxHeightUpTo(heights, j - 1) <= heights[j];
    } else {
      assert maxHeightUpTo(heights, j) == maxHeightUpTo(heights, j - 1);
    }
  }
}

lemma CanMakeNonDecreasingImpliesCondition(heights: seq<int>, i: int)
  requires |heights| > 0
  requires CanMakeNonDecreasing(heights)
  requires 0 <= i < |heights|
  ensures heights[i] >= maxHeightUpTo(heights, i) - 1
{
}

lemma ConditionImpliesCanMakeNonDecreasing(heights: seq<int>)
  requires |heights| > 0
  requires forall i :: 0 <= i < |heights| ==> heights[i] >= maxHeightUpTo(heights, i) - 1
  ensures CanMakeNonDecreasing(heights)
{
}

lemma MaxHeightUpToMonotonic(heights: seq<int>, j: int)
  requires |heights| > 0
  requires 0 <= j < |heights|
  ensures maxHeightUpTo(heights, j) >= maxHeightUpTo(heights, j - 1)
{
  if j > 0 {
    calc >= {
      maxHeightUpTo(heights, j);
      { if heights[j] > maxHeightUpTo(heights, j - 1) {
          assert maxHeightUpTo(heights, j) == heights[j];
        } else {
          assert maxHeightUpTo(heights, j) == maxHeightUpTo(heights, j - 1);
        }
      }
      maxHeightUpTo(heights, j - 1);
    }
  }
}

lemma MaxHeightUpToEq(heights: seq<int>, j: int)
  requires |heights| > 0
  requires 0 <= j < |heights|
  ensures maxHeightUpTo(heights, j) == 
    if j == 0 then heights[0]
    else max(maxHeightUpTo(heights, j - 1), heights[j])
{
  if j > 0 {
    if heights[j] > maxHeightUpTo(heights, j - 1) {
      assert maxHeightUpTo(heights, j) == heights[j];
    } else {
      assert maxHeightUpTo(heights, j) == maxHeightUpTo(heights, j - 1);
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
  var maxSoFar := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant maxSoFar == (if i == 0 then 0 else maxHeightUpTo(heights, i - 1))
  {
    if heights[i] < maxSoFar - 1 {
      result := "No";
      return;
    }
    
    // Update maxSoFar to be maxHeightUpTo(heights, i)
    if i == 0 {
      maxSoFar := heights[0];
    } else {
      MaxHeightUpToEq(heights, i);
      maxSoFar := max(maxSoFar, heights[i]);
    }
    
    i := i + 1;
  }
  
  // Prove the postcondition for "Yes" case
  ConditionImpliesCanMakeNonDecreasing(heights);
  result := "Yes";
}
// </vc-code>

