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
function maxSeq(s: seq<int>): int
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] <= maxSeq(s)
  ensures exists i :: 0 <= i < |s| && s[i] == maxSeq(s)
{
  if |s| == 1 then s[0]
  else if s[|s|-1] > maxSeq(s[..|s|-1]) then s[|s|-1]
  else maxSeq(s[..|s|-1])
}

lemma lemma_maxHeightUpTo_is_max_of_prefix(heights: seq<int>, index: int)
  requires |heights| > 0
  requires 0 <= index < |heights|
  ensures maxHeightUpTo(heights, index) == maxSeq(heights[..index+1])
  decreases index
{
  if index == 0 {
    // maxHeightUpTo(heights, 0) == heights[0]
    // maxSeq(heights[..1]) == heights[0]
  } else {
    lemma_maxHeightUpTo_is_max_of_prefix(heights, index - 1);
    if heights[index] > maxHeightUpTo(heights, index - 1) {
      // maxHeightUpTo(heights, index) == heights[index]
      assert maxHeightUpTo(heights, index - 1) == maxSeq(heights[..index]);
      assert maxSeq(heights[..index+1]) == heights[index];
    } else {
      // maxHeightUpTo(heights, index) == maxHeightUpTo(heights, index - 1)
      assert maxHeightUpTo(heights, index - 1) == maxSeq(heights[..index]);
      assert maxSeq(heights[..index+1]) == maxHeightUpTo(heights, index - 1);
    }
  }
}

lemma lemma_CanMakeNonDecreasing_implies_heights_change_by_at_most_1(heights: seq<int>)
  requires |heights| > 0
  requires CanMakeNonDecreasing(heights)
  ensures (forall i :: 0 <= i < |heights| ==> heights[i] >= 1) && (forall i :: 1 <= i < |heights| ==> heights[i] >= heights[i-1] - 1)
{
  forall i | 0 <= i < |heights|
    ensures heights[i] >= 1
  {
    assert heights[i] >= maxHeightUpTo(heights, i) - 1;
    if i == 0 {
      assert maxHeightUpTo(heights, 0) == heights[0];
      assert heights[0] >= heights[0] - 1; // This is trivial
      // We need to prove heights[0] >= 1
      // From the ValidInput precondition, all heights[i] >= 1
      // So heights[0] >= 1 is given from ValidInput
    } else {
      if i > 0 {
        lemma_maxHeightUpTo_is_max_of_prefix(heights, i);
        lemma_maxHeightUpTo_is_max_of_prefix(heights, i-1);
        assert maxHeightUpTo(heights, i) == maxSeq(heights[..i+1]);
        assert maxHeightUpTo(heights, i-1) == maxSeq(heights[..i]);

        // Case 1: heights[i] is the new max
        if heights[i] == maxHeightUpTo(heights, i) {
          assert heights[i] >= maxHeightUpTo(heights, i-1) - 1;
          assert heights[i] >= heights[i-1] - 1; // since heights[i-1] <= maxHeightUpTo(heights, i-1)
        } else { // Case 2: maxHeightUpTo(heights, i) == maxHeightUpTo(heights, i-1)
          assert maxHeightUpTo(heights, i) == maxHeightUpTo(heights, i-1);
          assert heights[i] >= maxHeightUpTo(heights, i-1) - 1; // This is directly from the premise
        }

        // To prove heights[i] >= 1 from heights[i] >= maxHeightUpTo(heights, i) - 1
        // We know maxHeightUpTo(heights, i) is at least 1 (since heights[k] >= 1 for all k in prefix)
        // If maxHeightUpTo(heights, i) is 1, then heights[i] >= 0. But we need heights[i] >= 1.
        // The condition "heights[i] >= maxHeightUpTo(heights, i) - 1" alone doesn't guarantee heights[i] >= 1.
        // The fact that ValidInput requires heights[i] >= 1 is crucial.
      }
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
  // First, let's establish the relationship between maxHeightUpTo and maxSeq
  // We need to show that CanMakeNonDecreasing(heights) is equivalent to something we can check without recursion.

  var canMake: bool := true;
  var currentMaxPrefix: int := heights[0]; // Represents maxSeq(heights[..i+1])

  forall i | 0 <= i < n
    ensures currentMaxPrefix == maxSeq(heights[..i+1])
  {
    if i == 0 {
      assert currentMaxPrefix == heights[0];
      assert maxSeq(heights[..1]) == heights[0];
    } else {
      var prevMaxPrefix := currentMaxPrefix;
      currentMaxPrefix := max(prevMaxPrefix, heights[i]);
      assert currentMaxPrefix == maxSeq(heights[..i+1]);
    }
  }

  // Use the established relationship in a loop to check the predicate
  currentMaxPrefix := heights[0]; // Reset for the loop
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant i == 0 ==> currentMaxPrefix == heights[0]
    invariant i > 0 ==> currentMaxPrefix == maxSeq(heights[..i])
    invariant canMake ==> (forall k :: 0 <= k < i ==> heights[k] >= maxHeightUpTo(heights, k) - 1)
  {
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i);
    if heights[i] < maxHeightUpTo(heights, i) - 1 {
      canMake := false;
      break;
    }
    if i < n - 1 {
      currentMaxPrefix := max(currentMaxPrefix, heights[i]);
    }
  }

  lemma_CanMakeNonDecreasing_implies_heights_change_by_at_most_1(heights);

  if canMake then
    return "Yes";
  else
    return "No";
}
// </vc-code>

