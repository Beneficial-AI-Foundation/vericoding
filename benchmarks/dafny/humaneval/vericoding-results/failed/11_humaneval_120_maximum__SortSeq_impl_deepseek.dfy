// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added complete bubble sort helper functions */
function swap(s: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |s| && 0 <= j < |s|
{
  s[i := s[j]][j := s[i]]
}

lemma SwapPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(swap(s, i, j)) == multiset(s)
{
}

lemma SwapPreservesLength(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures |swap(s, i, j)| == |s|
{
}

lemma SortedInvariantMaintained(sorted: seq<int>, j: int)
  requires |sorted| > 0 && 0 <= j < |sorted| - 1
  requires sorted[j] > sorted[j + 1]
  ensures forall k :: 0 <= k < j ==> swap(sorted, j, j + 1)[k] <= swap(sorted, j, j + 1)[k + 1]
{
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
/* code modified by LLM (iteration 5): Complete bubble sort implementation with proper invariants */
{
  sorted := s;
  var n := |sorted|;
  
  if n == 0 {
    return;
  }
  
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == n
    invariant multiset(sorted) == multiset(s)
    invariant forall x :: x in s ==> x in sorted
    invariant forall x :: x in sorted ==> x in s
    invariant forall p, q :: 0 <= p < q < n && q >= n - i ==> sorted[p] <= sorted[q]
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant |sorted| == n
      invariant multiset(sorted) == multiset(s)
      invariant forall x :: x in s ==> x in sorted
      invariant forall x :: x in sorted ==> x in s
      invariant forall p, q :: 0 <= p < q < n && q >= n - i ==> sorted[p] <= sorted[q]
      invariant forall k :: 0 <= k < j ==> sorted[k] <= sorted[k + 1]
    {
      if sorted[j] > sorted[j + 1] {
        sorted := swap(sorted, j, j + 1);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
