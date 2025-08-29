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
// Helper predicate to check if a sequence is sorted
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper lemma to ensure sequence length and multiset properties are maintained
lemma SwapPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
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
  ensures IsSorted(sorted)
  ensures multiset(sorted) == multiset(s)
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var n := |s|;
  if n <= 1 {
    return;
  }
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant IsSorted(sorted[..i])
    invariant multiset(sorted) == multiset(s)
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i <= minIndex < n
      invariant i <= j <= n
      invariant forall k :: i <= k < j && k < n ==> sorted[minIndex] <= sorted[k]
      invariant multiset(sorted) == multiset(s)
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]];
      sorted := sorted[minIndex := temp];
    }
    i := i + 1;
  }
}
// </vc-code>
