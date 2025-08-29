// <vc-helpers>
function IsThirdIndex(i: int): bool
{
  i % 3 == 0
}

lemma ThirdIndexPreservation(a: seq<int>, sorted: seq<int>)
  requires |a| == |sorted|
  requires multiset(a) == multiset(sorted)
  requires forall i, j :: 0 <= i < j < |sorted| && IsThirdIndex(i) && IsThirdIndex(j) ==> sorted[i] <= sorted[j]
  requires forall i :: 0 <= i < |a| && !IsThirdIndex(i) ==> sorted[i] == a[i]
  ensures forall i, j :: 0 <= i < j < |sorted| && i % 3 == 0 && j % 3 == 0 ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted[i] == a[i]
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var pred: seq<bool> := seq(|a|, i => IsThirdIndex(i));
  sorted_even := SortSeqPred(a, pred);
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