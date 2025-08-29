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
  assert forall x :: x in s <==> x in multiset(s);
  assert forall x :: x in sorted <==> x in multiset(sorted);
}

lemma SwapPreservesMultiset<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}

lemma InsertionStepPreservesOrder(sorted: seq<int>, i: int, j: int)
  requires 0 <= j < i < |sorted|
  requires forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
  requires sorted[j] > sorted[j+1]
  ensures forall x, y :: 0 <= x < y < i && (x != j || y != j+1) ==> sorted[x] <= sorted[y]
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
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
  ensures |s| == |sorted|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  if |sorted| <= 1 {
    MultisetPreservation(s, sorted);
    return;
  }
  
  var i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant multiset(s) == multiset(sorted)
    invariant |sorted| == |s|
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant multiset(s) == multiset(sorted)
      invariant |sorted| == |s|
      invariant forall x, y :: 0 <= x < y < i && y <= j ==> sorted[x] <= sorted[y]
      invariant forall x, y :: 0 <= x < y < i && x >= j ==> sorted[x] <= sorted[y]
      invariant forall k :: j < k <= i ==> (j == 0 || sorted[j-1] <= sorted[k])
    {
      SwapPreservesMultiset(sorted, j-1, j);
      var temp := sorted[j];
      sorted := sorted[j := sorted[j-1]];
      sorted := sorted[j-1 := temp];
      j := j - 1;
    }
    i := i + 1;
  }
  MultisetPreservation(s, sorted);
}
// </vc-code>
