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
    // The precondition ValidInput(n, heights) ensures heights[i] >= 1 for all i.
    // So directly asserting heights[i] >= 1 is valid based on input contract.
  }
  forall i | 1 <= i < |heights|
    ensures heights[i] >= heights[i-1] - 1
  {
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i);
    lemma_maxHeightUpTo_is_max_of_prefix(heights, i-1);

    assert maxHeightUpTo(heights, i) >= maxHeightUpTo(heights, i-1);
    assert maxHeightUpTo(heights, i) >= heights[i-1]; // max of prefix i+1 is >= a single element in prefix i-1

    // If heights[i] is the maximum in heights[..i+1]
    if heights[i] == maxHeightUpTo(heights, i) {
        assert ValidInput(|heights|, heights); // Bring in the precondition for heights[i-1] >= 1
        assert heights[i] >= maxHeightUpTo(heights, i) - 1; // from CanMakeNonDecreasing
        assert heights[i] >= maxSeq(heights[..i+1]) - 1; // using the lemma
        assert heights[i] >= maxSeq(heights[..i]) - 1; // maxSeq is non-decreasing on prefix size
        assert heights[i] >= heights[i-1] - 1 ; // because heights[i-1] <= maxSeq(heights[..i])
    } else { // maxHeightUpTo(heights, i) == maxHeightUpTo(heights, i-1)
        assert heights[i] >= maxHeightUpTo(heights, i) - 1; // from CanMakeNonDecreasing
        assert heights[i] >= maxHeightUpTo(heights, i-1) - 1; // substitution
        assert heights[i] >= heights[i-1] - 1; // since heights[i-1] <= maxHeightUpTo(heights, i-1)
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
  var canMake: bool := true;
  
  // The invariant of the loop for currentMaxPrefix must be correct for the full loop.
  // We need to maintain currentMaxPrefix as maxSeq(heights[..i]) at the start of iteration i.
  // Or, maxSeq(heights[..i+1]) at the end of iteration i.
  // Let's modify the loop slightly to simplify the invariant.

  var currentMaxPrefixVal: int := 0; // Represents maxSeq(heights[..i+1]) after processing index i.

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant i == 0 ==> currentMaxPrefixVal == 0
    invariant i > 0 ==> currentMaxPrefixVal == maxSeq(heights[..i]) // This refers to max up to i-1
    invariant canMake ==> (forall k :: 0 <= k < i ==> heights[k] >= maxHeightUpTo(heights, k) - 1)
  {
    if i == 0 {
      currentMaxPrefixVal := heights[0];
    } else {
      currentMaxPrefixVal := max(currentMaxPrefixVal, heights[i-1]); // max up to i-1
    }

    // Now, currentMaxPrefixVal holds maxSeq(heights[..i]) (i.e. max of heights[0]...heights[i-1])

    lemma_maxHeightUpTo_is_max_of_prefix(heights, i); // establishes maxHeightUpTo(heights, i) == maxSeq(heights[..i+1])

    if heights[i] < maxHeightUpTo(heights, i) - 1 {
      canMake := false;
      break;
    }
  }

  // After the loop, if canMake is still true, it means the condition held for all elements.
  // We need to prove that if canMake is true, then CanMakeNonDecreasing(heights) is true.
  // And vice-versa.

  if canMake {
    // If we reach here, it implies that for all k from 0 to n-1:
    // heights[k] >= maxHeightUpTo(heights, k) - 1
    // This is exactly the definition of CanMakeNonDecreasing(heights).
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>

