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
predicate isSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method SortSeqImpl(s: seq<int>) returns (sorted: seq<int>)
  ensures isSorted(sorted)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 {
    sorted := [];
  } else {
    var pivot := s[0];
    var less, greater := [], [];
    for i := 1 to |s|
      invariant |less| + |greater| == i - 1
      invariant multiset(less + greater) == multiset(s[1..i])
    {
      if s[i] <= pivot {
        less := less + [s[i]];
      } else {
        greater := greater + [s[i]];
      }
    }
    var sortedLess := SortSeqImpl(less);
    var sortedGreater := SortSeqImpl(greater);
    sorted := sortedLess + [pivot] + sortedGreater;
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  var sortedSeq := SortSeqImpl(s);
  return sortedSeq[..k];
}
// </vc-code>

