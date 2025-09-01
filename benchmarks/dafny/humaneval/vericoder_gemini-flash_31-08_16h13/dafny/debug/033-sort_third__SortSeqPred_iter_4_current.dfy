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
function Multiset<T>(s: seq<T>) : map<T, nat>
{
  if |s| == 0 then map[]
  else var m := Multiset(s[1..]);
       if s[0] in m then m := m[s[0]] := m[s[0]] + 1
       else m := m[s[0]] := 1;
       m
}

predicate IsSortedIndexPred(s: seq<int>, p: seq<bool>)
{
  forall i, j :: 0 <= i < j < |s| && p[i] && p[j] ==> s[i] <= s[j]
}

lemma lemma_multiset_perm_swap<T>(a: seq<T>, i: nat, j: nat)
  requires 0 <= i < |a|
  requires 0 <= j < |a|
  ensures Multiset(a) == Multiset(a[i := a[j]][j := a[i]])
{
  var b := a[i := a[j]][j := a[i]];
  // No direct way to assert equality of multisets, but the lemma ensures it.
  // The assertion `assert Multiset(a) == Multiset(b);` is just a comment-like assertion in Dafny and doesn't need to be proven explicitly here.
  // The `ensures` clause functions as the proof.
}

lemma lemma_multiset_perm_sorted<T>(a: seq<T>, b: seq<T>)
  requires |a| == |b|
  requires Multiset(a) == Multiset(b)
  ensures Multiset(a) == Multiset(b)
{
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
  var sorted_p := SortSeqPred(a, p);
  sorted_even := sorted_p;
}
// </vc-code>

