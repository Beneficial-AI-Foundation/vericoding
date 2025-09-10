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

function max(a: int, b: int): int
{
  if a > b then a else b
}

lemma lemma_maxHeightUpTo_is_max_of_prefix(heights: seq<int>, index: int)
  requires |heights| > 0
  requires -1 <= index < |heights|
  ensures index < 0 ==> maxHeightUpTo(heights, index) == 0
  ensures index >= 0 ==> maxHeightUpTo(heights, index) == maxSeq(heights[..index+1])
  decreases index
{
  if index < 0 {
    // handled by ensures index < 0 ...
  } else if index == 0 {
    // maxHeightUpTo(heights, 0) == heights[0]
    // maxSeq(heights[..1]) == heights[0]
  } else {
    lemma_maxHeightUpTo_is_max_of_prefix(heights, index - 1);
    // if heights[index] > maxHeightUpTo(heights, index - 1) {
    //   // maxHeightUpTo(heights, index) == heights[index]
    //   assert maxHeightUpTo(heights, index - 1) == maxSeq(heights[..index]);
    //   assert maxSeq(heights[..index+1]) == heights[index];
    // } else {
    //   // maxHeightUpTo(heights, index) == maxHeightUpTo(heights, index - 1)
    //   assert maxHeightUpTo(heights, index - 1) == maxSeq(heights[..index]);
    //   assert maxSeq(heights[..index+1]) == maxHeightUpTo(heights, index - 1);
    // }
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
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i);
    if i == 0 {
        assert heights[0] >= maxHeightUpTo(heights, 0) - 1;
        assert heights[0] >= heights[0] -1;
    } else {
        assert heights[0] >= 1; // from ValidInput
        assert maxHeightUpTo(heights, i) >= heights[0]; // because heights[0] is in the prefix
        assert heights[i] >= maxHeightUpTo(heights, i) - 1;
        assert heights[i] >= heights[0] - 1;
        if heights[i] >= 1 {} else {
            // This needs to be shown based on initial heights[k] >= 1 and the condition itself
            // If heights[i] = 0, then maxHeightUpTo(heights, i) can be at most 1.
            // If maxHeightUpTo(heights, i) = 1, then heights[k] = 1 for some k <= i
            // If heights[i] = 0, then heights[i] >= maxHeightUpTo(heights, i) - 1 implies 0 >= maxHeightUpTo(heights, i) - 1 => maxHeightUpTo(heights, i) <= 1
            // If maxHeightUpTo(heights, i) = 0 then all heights in [0..i] are 0. but valid input implies heights[0] >= 1.
            // So if `heights[0]` is allowed to be 0 by `CanMakeNonDecreasing`, then `heights[0] >= 1` in ValidInput is crucial.
        }
    }
  }
  forall i | 1 <= i < |heights|
    ensures heights[i] >= heights[i-1] - 1
  {
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i);
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i-1);

    assert maxHeightUpTo(heights, i) >= maxHeightUpTo(heights, i-1);
    
    // We know heights[i] >= maxHeightUpTo(heights, i) - 1
    // We want to show heights[i] >= heights[i-1] - 1
    // Proof:
    // maxHeightUpTo(heights, i) is the max of heights[0..i].
    // This value is either heights[i] itself or maxHeightUpTo(heights, i-1).
    // Case 1: maxHeightUpTo(heights, i) == heights[i]
    //   Then heights[i] >= heights[i] - 1 (which is trivially true, but not what we need for heights[i-1])
    //   We know heights[i-1] <= maxHeightUpTo(heights, i-1) because maxHeightUpTo calculates max.
    //   And maxHeightUpTo(heights, i-1) <= maxHeightUpTo(heights, i) if heights[i] is positive, or elements before i are large
    // Case 2: maxHeightUpTo(heights, i) == maxHeightUpTo(heights, i-1)
    //   Then heights[i] >= maxHeightUpTo(heights, i-1) - 1
    //   Since heights[i-1] <= maxHeightUpTo(heights, i-1), it follows that
    //   heights[i] >= heights[i-1] - 1 (QED for this case)

    // Let's use the property of maxSeq directly to be more direct instead of cases.
    // We know: heights[i] >= maxHeightUpTo(heights, i) - 1
    // By lemma: heights[i] >= maxSeq(heights[..i+1]) - 1
    // We also know: heights[i-1] <= maxSeq(heights[..i]) and maxSeq(heights[..i]) <= maxSeq(heights[..i+1])
    // So, heights[i-1] <= maxSeq(heights[..i+1]) (because max of a prefix is smaller or equal to max of a longer prefix)
    // Thus, if heights[i] will be compared with heights[i-1], the property of maxSeq of prefix applies.
    assert heights[i-1] <= maxHeightUpTo(heights, i); // Because heights[i-1] is part of heights[0..i]
    assert heights[i] >= maxHeightUpTo(heights, i) - 1;
    assert heights[i] >= heights[i-1] - 1; // Direct from the above two assertions
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
  var canMake: bool := true;

  var currentMaxPrefixVal: int := 0; 
  // Loop invariant: currentMaxPrefixVal stores maxSeq(heights[..i]) BEFORE processing heights[i]

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant i == 0 ==> currentMaxPrefixVal == 0
    invariant i > 0 ==> currentMaxPrefixVal == maxSeq(heights[..i])
    invariant canMake ==> (forall k :: 0 <= k < i ==> heights[k] >= maxHeightUpTo(heights, k) - 1)
  {
    if i == 0 {
      currentMaxPrefixVal := heights[0]; // At i=0, currentMaxPrefixVal represents maxSeq(heights[..1])
    } else {
      // At the start of this iteration 'i' (where i > 0):
      // currentMaxPrefixVal holds maxSeq(heights[..i]) (i.e., max of elements up to index i-1)
      // We need maxSeq(heights[..i+1]) for the next iteration (i.e. max of elements up to index 'i')
      lemma_maxHeightUpTo_is_max_of_prefix(heights, i-1); // establishes maxSeq(heights[..i]) == maxHeightUpTo(heights, i-1)
      currentMaxPrefixVal := max(currentMaxPrefixVal, heights[i]);
      // Now currentMaxPrefixVal holds maxSeq(heights[..i+1])
    }
    
    // Now, at the point of checks, `currentMaxPrefixVal` contains `maxSeq(heights[..i+1])`.
    // And maxHeightUpTo(heights, i) is also `maxSeq(heights[..i+1])`.
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i); 
    
    if heights[i] < maxHeightUpTo(heights, i) - 1 {
      canMake := false;
      break;
    }
  }

  if canMake {
    assert canMake ==> (forall k :: 0 <= k < n ==> heights[k] >= maxHeightUpTo(heights, k) - 1);
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>

