// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)

  requires |s| == |p|

  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l]
    invariant forall k, l :: 0 <= k < i && i <= l < |s| && p[k] && p[l] ==> sorted[k] <= sorted[l]
  {
    if p[i] {
      var min_idx := i;
      var j := i + 1;
      while j < |s|
        invariant i < j <= |s|
        invariant i <= min_idx < j
        invariant p[min_idx]
        invariant forall k :: i <= k < j && p[k] ==> sorted[min_idx] <= sorted[k]
      {
        if p[j] && sorted[j] < sorted[min_idx] {
          min_idx := j;
        }
        j := j + 1;
      }
      var temp := sorted[i];
      sorted := sorted[i := sorted[min_idx]];
      sorted := sorted[min_idx := temp];
    }
    i := i + 1;
  }
}
// </vc-code>
