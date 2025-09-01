

// <vc-helpers>
lemma MultisetPreservation(a: seq<int>, sorted: seq<int>, evenIndices: seq<int>)
  requires |sorted| == |a|
  requires forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  requires |a| > 0 ==> |evenIndices| == |a| / 2
  requires |a| > 0 ==> multiset(evenIndices) == multiset(seq(|a| / 2, i requires 0 <= i < |a| / 2 => a[2*i]))
  requires |a| > 0 ==> forall i :: 0 <= i < |evenIndices| && 2*i < |sorted| ==> sorted[2*i] == evenIndices[i]
  ensures multiset(a) == multiset(sorted)
{
  if |a| == 0 {
    return;
  }
  
  var evenElements := seq(|a| / 2, i requires 0 <= i < |a| / 2 => a[2*i]);
  var sortedEvenElements := seq(|a| / 2, i requires 0 <= i < |a| / 2 && 2*i < |sorted| => sorted[2*i]);
  
  assert multiset(evenElements) == multiset(evenIndices);
  assert multiset(sortedEvenElements) == multiset(evenIndices);
  
  var oddElementsA := seq((|a| + 1) / 2, i requires 0 <= i < (|a| + 1) / 2 => if 2*i + 1 < |a| then a[2*i + 1] else 0);
  var oddElementsSorted := seq((|a| + 1) / 2, i requires 0 <= i < (|a| + 1) / 2 => if 2*i + 1 < |a| then sorted[2*i + 1] else 0);
  
  assert forall i :: 0 <= i < (|a| + 1) / 2 && 2*i + 1 < |a| ==> sorted[2*i + 1] == a[2*i + 1];
  assert multiset(oddElementsA) == multiset(oddElementsSorted);
  
  assert multiset(a) == multiset(evenElements) + multiset(oddElementsA);
  assert multiset(sorted) == multiset(sortedEvenElements) + multiset(oddElementsSorted);
}

function ExtractEvenIndices(a: seq<int>): seq<int>
  requires |a| > 0
{
  seq(|a| / 2, i requires 0 <= i < |a| / 2 => a[2*i])
}

function InsertSortedEvens(a: seq<int>, sortedEvens: seq<int>): seq<int>
  requires |a| > 0
  requires |sortedEvens| == |a| / 2
  ensures |InsertSortedEvens(a, sortedEvens)| == |a|
  ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> InsertSortedEvens(a, sortedEvens)[i] == a[i]
  ensures forall i :: 0 <= i < |sortedEvens| && 2*i < |a| ==> InsertSortedEvens(a, sortedEvens)[2*i] == sortedEvens[i]
{
  seq(|a|, i requires 0 <= i < |a| => if i % 2 == 0 && i / 2 < |sortedEvens| then sortedEvens[i / 2] else a[i])
}

method SortSequence(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  if |s| == 0 {
    sorted := s;
    return;
  }
  
  sorted := s;
  var n := |sorted|;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |sorted| == n
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < i && i <= y < n ==> sorted[x] <= sorted[y]
    decreases n - 1 - i
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i <= minIndex < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
      decreases n - j
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