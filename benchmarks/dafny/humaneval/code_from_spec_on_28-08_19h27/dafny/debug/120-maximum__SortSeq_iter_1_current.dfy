method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservation(s: seq<int>, sorted: seq<int>)
  requires multiset(s) == multiset(sorted)
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
  ensures |s| == |sorted|
{
}

lemma SortedProperty(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  requires |s| >= 0
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant multiset(s) == multiset(sorted)
    invariant |sorted| == |s|
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant multiset(s) == multiset(sorted)
      invariant |sorted| == |s|
      invariant forall x, y :: 0 <= x < y < i && !(x == j-1 && y == j) ==> sorted[x] <= sorted[y]
    {
      var temp := sorted[j];
      sorted := sorted[j := sorted[j-1]];
      sorted := sorted[j-1 := temp];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
