// <vc-helpers>
// No additional helpers needed for this verification
// </vc-helpers>

// <vc-description>
/*
function_signature: method sorted_even(a: seq<int>) returns (sorted: seq<int>)
Sort elements. Requires: requires size of asize of  > 0. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  requires |a| > 0
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(sorted) == multiset(a)
// </vc-spec>
// <vc-code>
{
  var result: seq<int> := a;
  var n := |a|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: 0 <= k < l < i < n ==> result[k] <= result[l]
    invariant multiset(result) == multiset(a)
    invariant |result| == n
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i <= minIndex < n
      invariant i <= j <= n
      invariant forall k :: i <= k < j < n ==> result[minIndex] <= result[k]
      invariant multiset(result) == multiset(a)
      invariant |result| == n
    {
      if result[j] < result[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := result[i];
      result := result[i := result[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  sorted := result;
}
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}