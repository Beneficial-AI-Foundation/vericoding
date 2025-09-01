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
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var n := |s|;
  var indices := [i | i in 0..n-1 where p[i]];
  var vals := [s[i] | i in indices];
  vals := Seq.Sort(vals);
  sorted := s;
  var idx := 0;
  for i := 0 to n - 1 {
    if p[i] {
      sorted := sorted[0..i] + vals[idx] + sorted[i+1..];
      idx := idx + 1;
    }
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
var p := [i % 2 == 0 | i in 0..|a| - 1];
return SortSeqPred(a, p);
// </vc-code>

