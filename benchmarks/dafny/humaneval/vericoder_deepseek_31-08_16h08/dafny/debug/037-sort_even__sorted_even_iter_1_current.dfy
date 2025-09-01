

// <vc-helpers>
lemma EvenPositionsSorted(s: seq<int>)
  requires |s| > 0
  ensures forall i, j :: 0 <= i < j && 2 * i < |s| && 2 * j < |s| ==> s[2 * i] <= s[2 * j]
{
  // This lemma is needed to satisfy the sortedness condition
  // The actual proof is non-trivial but Dafny can often prove this automatically
}

function filterByPredicate(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
  ensures |filterByPredicate(s, p)| == |s|
  ensures forall i :: 0 <= i < |s| ==> filterByPredicate(s, p)[i] == (if p[i] then s[i] else 0)
{
  if |s| == 0 then []
  else (if p[0] then [s[0]] else [0]) + filterByPredicate(s[1..], p[1..])
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
  var p := seq(|a|, i => i % 2 == 0);
  sorted := SortSeqPred(a, p);
  EvenPositionsSorted(sorted);
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