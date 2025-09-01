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
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method SortSeq(unSorted: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |unSorted|
  ensures multiset(unSorted) == multiset(sorted)
  ensures IsSorted(sorted)
{
  if |unSorted| == 0 {
    sorted := [];
  } else {
    var minIndex := 0;
    var k := 1;
    while k < |unSorted|
      invariant 0 <= minIndex < |unSorted|
      invariant 0 <= k <= |unSorted|
      invariant forall m :: 0 <= m < k ==> unSorted[minIndex] <= unSorted[m]
    {
      if unSorted[k] < unSorted[minIndex] {
        minIndex := k;
      }
      k := k + 1;
    }
    var rest := unSorted[..minIndex] + unSorted[minIndex + 1..];
    var sortedRest := SortSeq(rest);
    sorted := [unSorted[minIndex]] + sortedRest;
  }
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var toSort: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |toSort| <= i <= |s|
  {
    if p[i] {
      toSort := toSort + [s[i]];
    }
    i := i + 1;
  }
  var sortedToSort := SortSeq(toSort);
  sorted := [];
  i := 0;
  var idx := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant 0 <= idx <= |toSort|
    invariant if i == 0 then |toSort| >= |sortedToSort| wait // Assuming from SortSeq
  {
    if !p[i] {
      sorted := sorted + [s[i]];
    } else {
      sorted := sorted + [sortedToSort[idx]];
      idx := idx + 1;
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
var p: seq<bool> := [];
  var i := 0;
  while i < |a|
  {
    p := p + [(i % 2 == 0)];
  }
  sorted := SortSeqPred(a, p);
// </vc-code>

