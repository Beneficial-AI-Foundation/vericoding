

// <vc-helpers>
method Sort(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  var a: array<int> := new int[|s|];
  forall i | 0 <= i < |s| { a[i] := s[i]; }
  var n := a.Length;
  for i := 0 to n - 1 {
    var min_index := i;
    for j := i + 1 to n {
      if a[j] < a[min_index] {
        min_index := j;
      }
    }
    var temp := a[i];
    a[i] := a[min_index];
    a[min_index] := temp;
  }
  sorted := a[..];
}
// </vc-helpers>
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
var p := seq(|a|, i => i % 2 == 0);
  var to_sort: seq<int> := [];
  for i := 0 to |a| {
    if p[i] {
      to_sort := to_sort + [a[i]];
    }
  }
  var sorted_to_sort := Sort(to_sort);
  var result: seq<int> := [];
  var idx := 0;
  for i := 0 to |a| {
    if p[i] {
      result := result + [sorted_to_sort[idx]];
      idx := idx + 1;
    } else {
      result := result + [a[i]];
    }
  }
  sorted := result;
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