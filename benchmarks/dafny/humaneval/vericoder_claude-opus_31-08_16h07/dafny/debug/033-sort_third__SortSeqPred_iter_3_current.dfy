method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
method SortExtracted(vals: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |vals|
  ensures multiset(vals) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  sorted := vals;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |vals|
    invariant multiset(sorted) == multiset(vals)
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
  {
    var minIdx := i;
    var j := i + 1;
    while j < |sorted|
      invariant i < j <= |sorted|
      invariant i <= minIdx < |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var extracted := [];
  var indices := [];
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |extracted| == |indices|
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < i
    invariant forall j :: 0 <= j < |indices| ==> p[indices[j]]
    invariant forall j :: 0 <= j < |indices| ==> extracted[j] == s[indices[j]]
    invariant forall j, k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
    invariant forall j :: 0 <= j < |indices| ==> indices[j] < |s|
    invariant multiset(extracted) <= multiset(s)
  {
    if p[i] {
      extracted := extracted + [s[i]];
      indices := indices + [i];
    }
    i := i + 1;
  }
  
  var sortedExtracted := SortExtracted(extracted);
  
  sorted := s;
  i := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant |sorted| == |s|
    invariant |sortedExtracted| == |extracted|
    invariant |extracted| == |indices|
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < |s|
    invariant forall j :: 0 <= j < i ==> sorted[indices[j]] == sortedExtracted[j]
    invariant forall j :: i <= j < |indices| ==> sorted[indices[j]] == s[indices[j]]
    invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
    invariant forall j, k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
    invariant forall j :: 0 <= j < |indices| ==> p[indices[j]]
    invariant multiset(sortedExtracted) == multiset(extracted)
    invariant forall j, k :: 0 <= j < k < |sortedExtracted| ==> sortedExtracted[j] <= sortedExtracted[k]
    invariant multiset(sorted) == multiset(s)
    invariant forall j, k :: 0 <= j < k < i && 0 <= indices[j] < |sorted| && 0 <= indices[k] < |sorted| ==> sorted[indices[j]] <= sorted[indices[k]]
  {
    sorted := sorted[indices[i] := sortedExtracted[i]];
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < |indices| ==> sorted[indices[j]] == sortedExtracted[j];
  assert forall j, k :: 0 <= j < k < |sortedExtracted| ==> sortedExtracted[j] <= sortedExtracted[k];
  assert forall j, k :: 0 <= j < k < |sorted| && p[j] && p[k] ==> 
    exists jj, kk :: 0 <= jj < kk < |indices| && indices[jj] == j && indices[kk] == k && sorted[j] <= sorted[k];
}
// </vc-code>

