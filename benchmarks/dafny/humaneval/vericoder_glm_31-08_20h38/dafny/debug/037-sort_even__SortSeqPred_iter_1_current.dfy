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
  {
    if p[2*i] && p[2*j] {
      assert sorted[2 * i] <= sorted[2 * j];
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
{
  var p := seq(|a|, i requires 0 <= i < |a| => i % 2 == 0);
  var s' := SortSeqPred(a, p);
  sorted := s';
  assert IsSortedEven(sorted) by {
    SortSeqPredImpliesSortedEven(a, p, s');
  }
}
// </vc-code>

