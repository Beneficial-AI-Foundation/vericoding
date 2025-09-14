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
    invariant forall i, x :: 0 <= i < |sorted| && x in remaining ==> sorted[i] <= x
  {
    var minIdx := FindMin(remaining);
    var minVal := remaining[minIdx];
    
    // Create new remaining sequence without the minimum element
    var newRemaining := remaining[..minIdx] + remaining[minIdx + 1..];
    
    // Use the lemma to maintain multiset invariant
    RemovePreservesMultiset(remaining, minIdx);
    assert multiset(remaining) == multiset([minVal]) + multiset(newRemaining);
    
    // The minimum value property ensures minVal is less than or equal to all elements in newRemaining
    assert forall x :: x in newRemaining ==> minVal <= x by {
      forall x | x in newRemaining {
        if x in remaining[..minIdx] {
          assert x == remaining[remaining[..minIdx].IndexOf(x)];
          assert minVal <= x;
        } else {
          assert x in remaining[minIdx + 1..];
          var j := remaining[minIdx + 1..].IndexOf(x);
          assert x == remaining[minIdx + 1 + j];
          assert minVal <= x;
        }
      }
    }
    
    // Update sorted and remaining
    sorted := sorted + [minVal];
    remaining := newRemaining;
    
    // Prove that sorted remains sorted
    assert IsSorted(sorted) by {
      // sorted[..|sorted|-1] was already sorted
      assert IsSorted(sorted[..|sorted|-1]);
      
      // All elements in sorted[..|sorted|-1] are <= minVal due to the loop invariant
      if |sorted| > 1 {
        var prevSorted := sorted[..|sorted|-1];
        assert prevSorted == old(sorted);
        forall i | 0 <= i < |prevSorted| {
          assert prevSorted[i] <= minVal by {
            assert minVal in old(remaining);
            assert prevSorted[i] <= minVal;
          }
        }
      }
      
      // Therefore the full sorted sequence is sorted
      forall i, j | 0 <= i < j < |sorted| {
        if j < |sorted| - 1 {
          assert sorted[i] <= sorted[j];
        } else {
          assert j == |sorted| - 1;
          assert sorted[j] == minVal;
          assert sorted[i] <= minVal;
        }
      }
    }
  }
}
// </vc-code>

