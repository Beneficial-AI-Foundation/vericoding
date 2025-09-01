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
function method pred(i: int): bool {
  i % 3 == 0
}

lemma sorted_subsequence_multiset_lemma<T>(a: seq<T>, p: T -> bool, sorted_a: seq<T>)
  requires |a| == |sorted_a|
  requires forall i :: 0 <= i < |a| && !p(a[i]) ==> sorted_a[i] == a[i]
  requires forall i, j :: 0 <= i < j < |a| && p(a[i]) && p(a[j]) ==> sorted_a[i] <= sorted_a[j]
  requires multiset(a) == multiset(sorted_a)
  ensures multiset(a) == multiset(sorted_a)
{
  // This lemma is a tautology; it's here to provide a place if some
  // verification efforts need to be explicitly written to prove properties
  // related to `multiset` and `sorted_subsequence`.
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
  var p: seq<bool> := seq(|a|, i => i % 3 == 0);
  var sorted_subseq := SortSeqPred(a, p);
  return sorted_subseq;
}
// </vc-code>

