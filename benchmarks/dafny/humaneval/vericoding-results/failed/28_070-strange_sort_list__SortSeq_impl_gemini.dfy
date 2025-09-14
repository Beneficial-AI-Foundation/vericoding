// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [used a standard partition-based multiset invariant] */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant Sorted(sorted)
    invariant |sorted| == i
    invariant multiset(s) == multiset(sorted) + multiset(s[i..])
  {
    var x := s[i];
    var j := 0;
    while j < |sorted| && sorted[j] < x 
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> sorted[k] < x
    {
      j := j + 1;
    }
    sorted := sorted[..j] + [x] + sorted[j..];
    i := i + 1;
  }
}
// </vc-code>
