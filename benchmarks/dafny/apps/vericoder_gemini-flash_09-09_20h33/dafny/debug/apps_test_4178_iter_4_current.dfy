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
        // assert ValidInput(|heights|, heights); // Bring in the precondition for heights[i-1] >= 1
        assert heights[i] >= maxHeightUpTo(heights, i) - 1; // from CanMakeNonDecreasing
        assert heights[i] >= maxSeq(heights[..i+1]) - 1; // using the lemma
        assert heights[i] >= maxSeq(heights[..i]) - 1; // maxSeq is non-decreasing on prefix size
        calc {
            maxSeq(heights[..i]);
            max(maxSeq(heights[..i-1]), heights[i-1]);
        }
        assert heights[i-1] <= maxSeq(heights[..i]);
        assert heights[i] >= heights[i-1] - 1 ; // because heights[i-1] <= maxSeq(heights[..i])
    } else { // maxHeightUpTo(heights, i) == maxHeightUpTo(heights, i-1)
        assert heights[i] >= maxHeightUpTo(heights, i) - 1; // from CanMakeNonDecreasing
        assert heights[i] >= maxHeightUpTo(heights, i-1) - 1; // substitution
        assert heights[i-1] <= maxHeightUpTo(heights, i-1);
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
  
  var currentMaxPrefixVal: int := 0; 

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant i == 0 ==> currentMaxPrefixVal == 0
    invariant i > 0 ==> currentMaxPrefixVal == maxSeq(heights[..i])
    invariant canMake ==> (forall k :: 0 <= k < i ==> heights[k] >= maxHeightUpTo(heights, k) - 1)
  {
    if i == 0 {
      currentMaxPrefixVal := heights[0];
    } else {
      currentMaxPrefixVal := max(currentMaxPrefixVal, heights[i-1]); // max up to i-1
    }

    // Now, currentMaxPrefixVal holds maxSeq(heights[..i]) (i.e. max of heights[0]...heights[i-1])
    
    // We need currentMaxPrefixVal to be maxSeq(heights[..i]) before the body.
    // So the update needs to happen before checking the invariant for the next iteration.
    // The current loop invariant for i > 0 is correct if currentMaxPrefixVal is indeed maxSeq(heights[..i]) at the beginning of the loop for iteration i.

    // This loop structure is such that currentMaxPrefixVal at the beginning of iteration `i`
    // represents the max of `heights[0..i-1]`.
    // After the update: `currentMaxPrefixVal` now stores `maxSeq(heights[..i])`.

    lemma_maxHeightUpTo_is_max_of_prefix(heights, i); // establishes maxHeightUpTo(heights, i) == maxSeq(heights[..i+1])

    if heights[i] < maxHeightUpTo(heights, i) - 1 {
      canMake := false;
      break;
    }
  }

  if canMake {
    // If the loop finished and canMake is true, it means the condition held for all k < n.
    // This is exactly CanMakeNonDecreasing(heights)
    assert canMake ==> (forall k :: 0 <= k < n ==> heights[k] >= maxHeightUpTo(heights, k) - 1);
    return "Yes";
  } else {
    // If canMake is false, it was set due to heights[i] < maxHeightUpTo(heights, i) - 1
    // This directly contradicts CanMakeNonDecreasing(heights)
    return "No";
  }
}
// </vc-code>

