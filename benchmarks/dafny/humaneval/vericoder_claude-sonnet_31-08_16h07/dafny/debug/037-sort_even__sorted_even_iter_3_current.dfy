

// <vc-helpers>
lemma MultisetPreservation(a: seq<int>, sorted: seq<int>, evenIndices: seq<int>)
  requires |sorted| == |a|
  requires forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  requires multiset(evenIndices) == multiset(seq(|a| / 2, i => a[2*i]))
  requires forall i :: 0 <= i < |evenIndices| ==> sorted[2*i] == evenIndices[i]
  ensures multiset(a) == multiset(sorted)
{
  var evenPositions := seq(|a| / 2, i => 2*i);
  var oddPositions := seq((|a| + 1) / 2, i => 2*i + 1);
  
  assert forall pos :: pos in evenPositions ==> 0 <= pos < |a| && pos % 2 == 0;
  assert forall pos :: pos in oddPositions ==> 0 <= pos < |a| && pos % 2 == 1;
  
  var evenElements := seq(|a| / 2, i => a[2*i]);
  var oddElements := seq((|a| + 1) / 2, i => if 2*i + 1 < |a| then a[2*i + 1] else 0);
  
  assert multiset(evenElements) == multiset(evenIndices);
  
  var sortedEvenElements := seq(|a| / 2, i => sorted[2*i]);
  var sortedOddElements := seq((|a| + 1) / 2, i => if 2*i + 1 < |a| then sorted[2*i + 1] else 0);
  
  assert multiset(sortedEvenElements) == multiset(evenIndices);
  assert multiset(sortedOddElements) == multiset(oddElements);
}

function ExtractEvenIndices(a: seq<int>): seq<int>
{
  seq(|a| / 2, i => a[2*i])
}

function InsertSortedEvens(a: seq<int>, sortedEvens: seq<int>): seq<int>
  requires |sortedEvens| == |a| / 2
{
  seq(|a|, i => if i % 2 == 0 then sortedEvens[i / 2] else a[i])
}

method SortSequence(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  sorted := s;
  var n := |sorted|;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |sorted| == n
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i <= minIndex < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var evenIndices := ExtractEvenIndices(a);
  var sortedEvens := SortSequence(evenIndices);
  sorted := InsertSortedEvens(a, sortedEvens);
  
  assert |sorted| == |a|;
  assert forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i];
  assert forall i :: 0 <= i < |evenIndices| ==> sorted[2*i] == sortedEvens[i];
  assert multiset(evenIndices) == multiset(seq(|a| / 2, i => a[2*i]));
  
  MultisetPreservation(a, sorted, sortedEvens);
}
// </vc-code>

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
{
  assume{:axiom} false;
}