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
function method Multiset<T>(s: seq<T>) : map<T, nat>
{
  if |s| == 0 then map[]
  else var m := Multiset(s[1..]);
       if s[0] in m then m[s[0]] := m[s[0]] + 1
       else m[s[0]] := 1;
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
  assert Multiset(a) == Multiset(b);
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
  var sorted := a;
  var p: seq<bool> := [true; |a|]; // All elements initially considered for sorting
  for k := 0 to |a|
    decreases |a| - k
    invariant 0 <= k <= |a|
    invariant Multiset(sorted) == Multiset(a)
    invariant forall x :: 0 <= x < |a| && x % 3 != 0 ==> sorted[x] == a[x]
    invariant forall i, j :: 0 <= i < j < k && i % 3 == 0 && j % 3 == 0 ==> sorted[i] <= sorted[j]
  {
    var min_val := sorted[k];
    var min_idx := k;
    if k % 3 == 0 {
      for j := k + 1 to |a|
        decreases |a| - j
        invariant k < j <= |a|
        invariant Multiset(sorted) == Multiset(a)
        invariant forall x :: 0 <= x < |a| && x % 3 != 0 ==> sorted[x] == a[x]
        invariant forall i, v :: k < v < j && v % 3 == 0 && i % 3 == 0 ==> sorted[i] <= sorted[v]
        invariant min_idx % 3 == 0 ==> sorted[min_idx] == min_val
        invariant forall x :: k <= x < j && x % 3 == 0 ==> sorted[min_idx] <= sorted[x]
      {
        if j % 3 == 0 && sorted[j] < min_val {
          min_val := sorted[j];
          min_idx := j;
        }
      }

      if min_idx != k {
        var temp := sorted[k];
        sorted := sorted[k := sorted[min_idx]];
        sorted := sorted[min_idx := temp];
        lemma_multiset_perm_swap(a, k, min_idx); // This seems to be the one giving issues without proper Multiset definition
      }
    }
  }

  sorted_even := sorted;
}
// </vc-code>

