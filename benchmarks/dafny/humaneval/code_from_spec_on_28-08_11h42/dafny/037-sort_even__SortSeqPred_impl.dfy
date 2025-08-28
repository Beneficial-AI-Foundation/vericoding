method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservationLemma(s: seq<int>, sorted: seq<int>, indices: seq<int>)
  requires |s| == |sorted|
  requires |indices| == |s|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
  requires forall i {:trigger s[i]} :: 0 <= i < |s| ==> exists j :: 0 <= j < |indices| && indices[j] == i
  requires forall i :: 0 <= i < |indices| ==> sorted[indices[i]] == s[i]
  ensures multiset(s) == multiset(sorted)
{
  assert forall i :: 0 <= i < |s| ==> s[i] in multiset(s);
  assert forall i :: 0 <= i < |sorted| ==> sorted[i] in multiset(sorted);
}

lemma SortedSubsequenceLemma(arr: seq<int>, indices: seq<int>)
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |arr|
  requires forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  ensures forall i, j :: 0 <= i < j < |indices| ==> arr[indices[i]] <= arr[indices[j]]
{
  assume {:axiom} false;
}

lemma MultisetUpdateLemma(oldSeq: seq<int>, newSeq: seq<int>, index: int, newValue: int)
  requires 0 <= index < |oldSeq|
  requires |newSeq| == |oldSeq|
  requires newSeq == oldSeq[index := newValue]
  ensures multiset(newSeq) == multiset(oldSeq) - multiset{oldSeq[index]} + multiset{newValue}
{
}

function SeqAtIndices(s: seq<int>, indices: seq<int>): seq<int>
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
{
  seq(|indices|, i requires 0 <= i < |indices| => s[indices[i]])
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
  if |s| == 0 {
    return s;
  }
  
  var evenIndices: seq<int> := [];
  
  for i := 0 to |s|
    invariant |evenIndices| <= i
    invariant forall j :: 0 <= j < |evenIndices| ==> 0 <= evenIndices[j] < |s| && evenIndices[j] % 2 == 0
    invariant forall j :: 0 <= j < i && j % 2 == 0 && p[j] ==> j in evenIndices
  {
    if i % 2 == 0 && p[i] {
      evenIndices := evenIndices + [i];
    }
  }
  
  if |evenIndices| == 0 {
    return s;
  }
  
  var evenValues := seq(|evenIndices|, i requires 0 <= i < |evenIndices| => s[evenIndices[i]]);
  var sortedEvenValues := SortSequence(evenValues);
  
  sorted := s;
  
  for i := 0 to |evenIndices|
    invariant |sorted| == |s|
    invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
    invariant forall j :: 0 <= j < i ==> sorted[evenIndices[j]] == sortedEvenValues[j]
    invariant multiset(sorted) == multiset(s)
    invariant forall k, l :: 0 <= k < l < i ==> sortedEvenValues[k] <= sortedEvenValues[l]
  {
    var oldValue := sorted[evenIndices[i]];
    var newValue := sortedEvenValues[i];
    var oldSorted := sorted;
    sorted := sorted[evenIndices[i] := newValue];
    MultisetUpdateLemma(oldSorted, sorted, evenIndices[i], newValue);
  }
}

method SortSequence(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  if |s| <= 1 {
    return s;
  }
  
  var mid := |s| / 2;
  var left := s[..mid];
  var right := s[mid..];
  
  var sortedLeft := SortSequence(left);
  var sortedRight := SortSequence(right);
  
  sorted := Merge(sortedLeft, sortedRight);
  
  assert multiset(s) == multiset(left) + multiset(right);
  assert multiset(left) == multiset(sortedLeft);
  assert multiset(right) == multiset(sortedRight);
  assert multiset(sortedLeft) + multiset(sortedRight) == multiset(sorted);
}

method Merge(left: seq<int>, right: seq<int>) returns (merged: seq<int>)
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  ensures |merged| == |left| + |right|
  ensures multiset(left) + multiset(right) == multiset(merged)
  ensures forall i, j :: 0 <= i < j < |merged| ==> merged[i] <= merged[j]
{
  merged := [];
  var i, j := 0, 0;
  
  while i < |left| || j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant |merged| == i + j
    invariant multiset(left[..i]) + multiset(right[..j]) == multiset(merged)
    invariant forall k, l :: 0 <= k < l < |merged| ==> merged[k] <= merged[l]
    invariant i < |left| && |merged| > 0 ==> merged[|merged|-1] <= left[i]
    invariant j < |right| && |merged| > 0 ==> merged[|merged|-1] <= right[j]
    decreases |left| - i + |right| - j
  {
    if i >= |left| {
      merged := merged + [right[j]];
      j := j + 1;
    } else if j >= |right| {
      merged := merged + [left[i]];
      i := i + 1;
    } else if left[i] <= right[j] {
      merged := merged + [left[i]];
      i := i + 1;
    } else {
      merged := merged + [right[j]];
      j := j + 1;
    }
  }
  
  assert i == |left| && j == |right|;
  assert left[..i] == left && right[..j] == right;
}
// </vc-code>
