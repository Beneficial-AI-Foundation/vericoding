method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate IsSortedByPredicate(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
{
  forall i, j :: 0 <= i < j < |s| && p[i] && p[j] ==> s[i] <= s[j]
}

lemma MultisetPreservation(original: seq<int>, result: seq<int>)
  requires |original| == |result|
  requires multiset(original) == multiset(result)
  ensures forall x :: x in original <==> x in result
{
  forall x ensures x in original <==> x in result {
    if x in original {
      assert x in multiset(original);
      assert multiset(original) == multiset(result);
      assert x in multiset(result);
      assert x in result;
    }
    if x in result {
      assert x in multiset(result);
      assert multiset(original) == multiset(result);
      assert x in multiset(original);
      assert x in original;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
Sort elements. Requires: returns the correct size/count. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; returns a sorted permutation of the input; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures |sorted| == |p|
  ensures IsSortedByPredicate(sorted, p)
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  ensures forall x :: x in s <==> x in sorted
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < i && i <= y < |sorted| && p[x] && p[y] ==> sorted[x] <= sorted[y]
  {
    if p[i] {
      var minIdx := i;
      var j := i + 1;
      
      while j < |sorted|
        invariant i <= j <= |sorted|
        invariant i <= minIdx < j
        invariant p[minIdx]
        invariant forall k :: i <= k < j && p[k] ==> sorted[minIdx] <= sorted[k]
      {
        if p[j] && sorted[j] < sorted[minIdx] {
          minIdx := j;
        }
        j := j + 1;
      }
      
      if minIdx != i {
        var temp := sorted[i];
        var newSorted := sorted[i := sorted[minIdx]][minIdx := temp];
        assert multiset(sorted) == multiset(newSorted);
        sorted := newSorted;
      }
    }
    i := i + 1;
  }
  
  MultisetPreservation(s, sorted);
}
// </vc-code>
