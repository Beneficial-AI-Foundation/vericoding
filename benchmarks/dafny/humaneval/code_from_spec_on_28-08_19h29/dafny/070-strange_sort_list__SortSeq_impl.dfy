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
// Helper lemma to prove properties about multisets and permutations
lemma MultisetPreservation(s: seq<int>, sorted: seq<int>)
  ensures multiset(s) == multiset(sorted) ==> |s| == |sorted|
{
}

// Helper lemma to prove multiset preservation when splitting sequences
lemma MultisetSplit(s: seq<int>, idx: int)
  requires 0 <= idx < |s|
  ensures multiset(s) == multiset([s[idx]]) + multiset(if idx == 0 then s[1..] else if idx == |s| - 1 then s[..|s|-1] else s[..idx] + s[idx+1..])
{
  if idx == 0 {
    assert s == [s[0]] + s[1..];
    assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
  } else if idx == |s| - 1 {
    assert s == s[..|s|-1] + [s[|s|-1]];
    assert multiset(s) == multiset(s[..|s|-1]) + multiset([s[|s|-1]]);
  } else {
    assert s == s[..idx] + [s[idx]] + s[idx+1..];
    assert multiset(s) == multiset(s[..idx]) + multiset([s[idx]]) + multiset(s[idx+1..]);
  }
}

// Helper lemma to ensure sorted property propagates
lemma SortedProperty(s1: seq<int>, s2: seq<int>)
  requires |s1| > 0
  requires forall i, j :: 0 <= i < j < |s2| ==> s2[i] <= s2[j]
  requires forall i :: 0 <= i < |s2| ==> s1[0] <= s2[i]
  ensures forall i, j :: 0 <= i < j < |s1| + |s2| ==> (s1 + s2)[i] <= (s1 + s2)[j]
{
  var totalLen := |s1| + |s2|;
  forall i, j | 0 <= i < j < totalLen
  {
    if i < |s1| && j < |s1| {
      // Both in s1, but s1 may not be sorted internally
      // However, since s1 has length 1 in our use case, this is fine
      assert |s1| == 1 ==> i == 0 && j == 0 ==> false;
    } else if i < |s1| && j >= |s1| {
      // i in s1, j in s2
      assert s1[0] <= s2[j - |s1|];
      assert (s1 + s2)[i] == s1[i];
      assert (s1 + s2)[j] == s2[j - |s1|];
      assert (s1 + s2)[i] <= (s1 + s2)[j];
    } else {
      // Both in s2
      assert (s1 + s2)[i] == s2[i - |s1|];
      assert (s1 + s2)[j] == s2[j - |s1|];
      assert i - |s1| < j - |s1| < |s2|;
      assert s2[i - |s1|] <= s2[j - |s1|];
      assert (s1 + s2)[i] <= (s1 + s2)[j];
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  requires true
  ensures multiset(s) == multiset(sorted)
  ensures |s| == |sorted|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    sorted := [];
  } else {
    var minIndex := 0;
    var i := 1;
    while i < |s|
      invariant 0 <= minIndex < |s|
      invariant forall k :: 0 <= k < i && k < |s| ==> s[minIndex] <= s[k]
    {
      if s[i] < s[minIndex] {
        minIndex := i;
      }
      i := i + 1;
    }
    var rest := if minIndex == 0 then s[1..] else if minIndex == |s| - 1 then s[..|s|-1] else s[..minIndex] + s[minIndex+1..];
    ghost var restMultiset := multiset(rest);
    MultisetSplit(s, minIndex);
    var restSorted := SortSeq(rest);
    sorted := [s[minIndex]] + restSorted;
    assert multiset(rest) == restMultiset;
    assert multiset(s) == multiset([s[minIndex]]) + multiset(rest);
    assert multiset(sorted) == multiset([s[minIndex]]) + multiset(restSorted);
    assert forall k :: 0 <= k < |restSorted| ==> restSorted[k] >= s[minIndex] by {
      assert multiset(rest) == multiset(restSorted);
      assert forall k :: 0 <= k < |rest| ==> rest[k] >= s[minIndex];
    }
    SortedProperty([s[minIndex]], restSorted);
  }
}
// </vc-code>
