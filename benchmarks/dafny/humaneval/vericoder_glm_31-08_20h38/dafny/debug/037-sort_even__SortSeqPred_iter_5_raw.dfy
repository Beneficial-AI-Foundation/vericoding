
```vc-helpers
predicate IsSortedEven(a: seq<int>) {
  forall i, j :: 0 <= i < j && 2 * i < |a| && 2 * j < |a| ==> a[2 * i] <= a[2 * j]
}

lemma SortSeqPredImpliesSortedEven(s: seq<int>, p: seq<bool>, sorted: seq<int>)
  requires |s| == |p|
  requires |sorted| == |s|
  requires forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  requires multiset(s) == multiset(sorted)
  requires forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  requires forall i :: 0 <= i < |p| ==> p[i] <==> i % 2 == 0
  ensures IsSortedEven(sorted)
{
  forall i, j | 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted|
    ensures sorted[2*i] <= sorted[2*j]
  {
    assert p[2*i] by {
      calc {
        p[2*i];
        == (forall i :: 0 <= i < |p| ==> p[i] <==> i % 2 == 0)[2*i];
        true;
      }
    }
    assert p[2*j] by {
      calc {
        p[2*j];
        == (forall i :: 0 <= i < |p| ==> p[i] <==> i % 2 == 0)[2*j];
        true;
      }
    }
    assert sorted[2*i] <= sorted[2*j] by {
      assert 0 <= 2*i < 2*j < |sorted|;
      calc {
        sorted[2*i] <= sorted[2*j];
        <== (forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]);
        true;
      }
    }
  }
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  sorted := s;
  var toSort := [i | i in 0..|s| if p[i]];
  var sortedIndices := SortSeqIndicies(s, toSort);
  var i := 0;
  while i < |sortedIndices|
    invariant 0 <= i <= |sortedIndices|
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
    invariant forall k, l :: 0 <= k < l < i ==> sorted[sortedIndices[k]] <= sorted[sortedIndices[l]]
  {
    var j := i;
    while j > 0 && sorted[sortedIndices[j-1]] > sorted[sortedIndices[j]]
      invariant 0 <= j <= i
      invariant 0 <= i <= |sortedIndices|
      invariant multiset(s) == multiset(sorted)
      invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
      invariant forall k, l :: 0 <= k < l < i ==> (k != j-1 || l != j) ==> sorted[sortedIndices[k]] <= sorted[sortedIndices[l]]
    {
      var temp := sorted[sortedIndices[j]];
      sorted := sorted[sortedIndices[j-1] := sorted[sortedIndices[j]]];
      sorted := sorted[sortedIndices[j]