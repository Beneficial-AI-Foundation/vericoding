

```vc-helpers
method SortSeq(s: seq<int>) returns (t: seq<int>)
  ensures |t| == |s|
  ensures multiset(t) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]
{
  var n := |s|;
  var t := s;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant multiset(t) == multiset(s)
    invariant (forall k, l :: 0 <= k < l < i => t[k] <= t[l])
  {
    var j := i;
    while j > 0 && t[j-1] > t[j]
      invariant 0 <= j <= i+1
      invariant multiset(t) == multiset(s)
      invariant (forall k, l :: 0 <= k < l < j => t[k] <= t[l])
    {
      t := t[0..j-1] + [t[j], t[j-1]] + t[j+1..n];
      j := j - 1;
    }
    i := i + 1;
  }
  return t;
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var true_indices := [i | i in 0..|s| : p[i]];
  var true_vals := [s[i] | i in 0..|s| : p[i]];
  var sorted_true := SortSeq(true_vals);
  var res := [];
  var idx := 0;
  for k := 0 to |s| - 1
    invariant idx <= |