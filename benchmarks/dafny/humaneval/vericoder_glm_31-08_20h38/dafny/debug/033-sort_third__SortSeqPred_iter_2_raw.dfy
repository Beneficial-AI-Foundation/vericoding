
```vc-helpers
method sortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  var arr := new int[|s|];
  var n := |s|;
  if n == 0 {
    return [];
  }
  for i in 0..n
    invariant i <= n
    invariant forall k :: 0 <= k < i ==> arr[k] == s[k]
  {
    arr[i] := s[i];
  }
  for i in 0