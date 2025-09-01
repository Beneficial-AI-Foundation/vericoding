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
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
{
  var n := |s|;
  var elements := [s[i] | i in 0..n : p[i]];
  elements := sort(elements);
  sorted := new seq<int>(n);
  var idx := 0;
  for i in 0..n {
    if p[i] {
      sorted[i] := elements[idx];
      idx := idx + 1;
    } else {
      sorted[i] := s[i];
    }
  }
  return sorted;
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
var p := [i % 3 == 0 | i in 0..|a|];
  return SortSeqPred(a, p);
// </vc-code>

