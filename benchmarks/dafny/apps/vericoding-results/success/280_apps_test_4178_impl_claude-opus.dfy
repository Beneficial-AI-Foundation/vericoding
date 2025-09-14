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
lemma MaxHeightUpToProperties(heights: seq<int>, index: int)
  requires |heights| > 0
  requires 0 <= index < |heights|
  ensures maxHeightUpTo(heights, index) >= heights[index]
  ensures forall j :: 0 <= j <= index ==> maxHeightUpTo(heights, index) >= heights[j]
{
  if index == 0 {
    // Base case trivial
  } else {
    MaxHeightUpToProperties(heights, index - 1);
    // Recursive case follows from definition
  }
}

lemma MaxHeightMonotonic(heights: seq<int>, i: int, j: int)
  requires |heights| > 0
  requires 0 <= i <= j < |heights|
  ensures maxHeightUpTo(heights, i) <= maxHeightUpTo(heights, j)
  decreases j - i
{
  if i == j {
    // Base case: equal indices
  } else if i == j - 1 {
    // Adjacent indices - follows from definition
  } else {
    MaxHeightMonotonic(heights, i, j - 1);
    MaxHeightMonotonic(heights, j - 1, j);
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
  var canMake := true;
  var i := 0;
  
  while i < n && canMake
    invariant 0 <= i <= n
    invariant canMake <==> (forall j :: 0 <= j < i ==> heights[j] >= maxHeightUpTo(heights, j) - 1)
  {
    var maxSoFar := maxHeightUpTo(heights, i);
    if heights[i] < maxSoFar - 1 {
      canMake := false;
    }
    i := i + 1;
  }
  
  if canMake {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

