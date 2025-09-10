method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
// Helper predicate to check if a sequence is sorted
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper method to find the minimum element's index in a sequence
method FindMin(s: seq<int>) returns (minIndex: int)
  requires |s| > 0
  ensures 0 <= minIndex < |s|
  ensures forall i :: 0 <= i < |s| ==> s[minIndex] <= s[i]
{
  minIndex := 0;
  var i := 1;
  while i < |s|
    invariant 0 <= minIndex < i <= |s|
    invariant forall j :: 0 <= j < i ==> s[minIndex] <= s[j]
  {
    if s[i] < s[minIndex] {
      minIndex := i;
    }
    i := i + 1;
  }
}

// Helper lemma to prove that removing an element preserves multiset equality
lemma RemovePreservesMultiset(s: seq<int>, idx: int)
  requires 0 <= idx < |s|
  ensures multiset(s) == multiset([s[idx]]) + multiset(s[..idx] + s[idx+1..])
{
  if idx == 0 {
    assert s == [s[0]] + s[1..];
    assert s[..0] == [];
    assert s[..0] + s[1..] == s[1..];
  } else if idx == |s| - 1 {
    assert s == s[..|s|-1] + [s[|s|-1]];
    assert s[idx+1..] == [];
  } else {
    assert s == s[..idx] + [s[idx]] + s[idx+1..];
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var remaining := s;
  
  while |remaining| > 0
    invariant |sorted| + |remaining| == |s|
    invariant multiset(sorted) + multiset(remaining) == multiset(s)
    invariant IsSorted(sorted)
    invariant |sorted| > 0 && |remaining| > 0 ==> forall x :: x in remaining ==> sorted[|sorted| - 1] <= x
  {
    var minIdx := FindMin(remaining);
    var minVal := remaining[minIdx];
    
    // Create new remaining sequence without the minimum element
    var newRemaining := remaining[..minIdx] + remaining[minIdx + 1..];
    
    // Use the lemma to maintain multiset invariant
    RemovePreservesMultiset(remaining, minIdx);
    assert multiset(remaining) == multiset([minVal]) + multiset(newRemaining);
    
    // Update sorted and remaining
    sorted := sorted + [minVal];
    remaining := newRemaining;
    
    // The minimum value property
    assert forall x :: x in newRemaining ==> minVal <= x;
    
    // Assert that sorted remains sorted
    if |sorted| > 1 {
      assert IsSorted(sorted[..|sorted|-1]);
      assert forall i :: 0 <= i < |sorted| - 1 ==> sorted[i] <= minVal by {
        if |sorted| > 1 && |newRemaining| > 0 {
          assert forall x :: x in remaining ==> sorted[|sorted| - 2] <= x;
          assert minVal in remaining;
          assert sorted[|sorted| - 2] <= minVal;
        }
      }
    }
    assert IsSorted(sorted);
  }
}
// </vc-code>

