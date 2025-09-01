

// <vc-helpers>
lemma MultisetPreservation(a: seq<int>, sorted: seq<int>, evenIndices: seq<int>)
  requires |sorted| == |a|
  requires forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  requires multiset(evenIndices) == multiset(seq(|a| / 2, i => a[2*i]))
  requires forall i :: 0 <= i < |evenIndices| ==> sorted[2*i] == evenIndices[i]
  ensures multiset(a) == multiset(sorted)
{
  // This lemma helps prove multiset preservation
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